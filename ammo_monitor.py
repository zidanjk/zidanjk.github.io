#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
三角洲行动 · 交易行子弹价格实时监控
================================================

特点
----
* 纯标准库实现，不依赖 requests / flask / pandas，装好 Python 即可运行
* 后台定时抓取，SQLite 落库积累历史价，浏览器里看板实时轮询
* 关注清单 + 触发条件（跌破买价 / 到卖出目标 / 单日异动 / 单次跳变）
* 触发时页面高亮闪烁 + 提示音（不弹系统通知）
* 支持按口径快刷关注子弹，支持 CSV 导出、手动校准单价

数据来源
--------
主源：https://6ow.cc（酸角洲数据站）的交易行行情接口。站点前端用 HMAC 签名
调 /api/act.php，本程序用标准库复刻同一套签名，一次请求即返回全量物品
（含子弹 80+ 种）的实时价、日涨跌、当日高/低。免登录、延迟低（约 1 分钟）。
这是第三方对游戏内交易行的镜像，不是官方接口；站点若改版，适配层需同步调整。

备源：https://orzice.com/v/ammo 的服务端直出页面。注意该站现在对未登录访客
隐藏实时价（显示“登陆查看价格”），需要登录后在 config.json 填 cookie 才能用。

用法
----
    python ammo_monitor.py            # 启动并自动打开浏览器
    python ammo_monitor.py --no-open  # 只启动服务
    python ammo_monitor.py --once     # 只跑一次全量扫描后退出

作者：Doubao Agent 生成，可自由修改。
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import hmac
import http.cookiejar
import json
import logging
import os
import random
import re
import secrets
import socket
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.request
import webbrowser
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from logging.handlers import RotatingFileHandler
from urllib.parse import parse_qs, quote, urlparse

APP_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(APP_DIR, "data")
DB_PATH = os.path.join(DATA_DIR, "monitor.db")
LOG_PATH = os.path.join(DATA_DIR, "monitor.log")
WEB_DIR = os.path.join(APP_DIR, "web")
CONFIG_PATH = os.path.join(APP_DIR, "config.json")

SOURCE_BASE = "https://orzice.com/v/ammo"
UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
)

# --------------------------------------------------------------------------
# 默认配置
# --------------------------------------------------------------------------
DEFAULT_SETTINGS: dict = {
    "port": 8777,
    "full_scan_interval": 300,   # 全市场扫描间隔（秒），最低 60
    "watch_interval": 60,        # 关注清单快刷间隔（秒），最低 30
    "request_gap_ms": 1100,      # 翻页请求间隔（毫秒），别调太低，对站点不礼貌
    "alert_jump_pct": 3.0,       # 单次扫描价格变化超过该百分比 -> 跳变提醒
    "alert_day_pct": 8.0,        # 当日涨跌幅超过该百分比 -> 异动提醒
    "alert_cooldown_min": 30,    # 同一物品同一类提醒的冷却时间（分钟）
    "fee_rate": 5.0,             # 交易行手续费率（%），用于利润测算
    "sound": True,               # 页面提示音
    "flash": True,               # 页面高亮闪烁
    "max_pages": 14,             # 全量扫描最多翻多少页
    "cookie": "",                # 备用源 orzice 的登录 Cookie（主源不需要）
    "source": "6ow",             # 数据源：6ow（免登录实时） / orzice（需 cookie）
    "sim_initial_cash": 1000000, # 模拟盘初始资金（元）
    # 模拟盘手续费按游戏内交易行规则：买入按挂牌价直接成交（不收），
    # 卖出扣 3% 保证金 + 10% 交易手续费，成交后结算，实测到手约 86%。
    "sim_buy_fee_pct": 0.0,
    "sim_sell_fee_pct": 15.0,
    # 分享给他人访问时用：
    "host": "127.0.0.1",         # 监听地址；本机自用 127.0.0.1，对局域网/公网开放改 0.0.0.0
    "share_token": "",           # 访问口令；留空=不校验（仅本机用），填了就要先输口令
    "readonly": False,           # 只读模式：拦住所有写接口，访客只能看行情
}
SETTING_LABELS = {
    "port": "服务端口",
    "full_scan_interval": "全市场扫描间隔（秒）",
    "watch_interval": "关注清单快刷间隔（秒）",
    "request_gap_ms": "翻页请求间隔（毫秒）",
    "alert_jump_pct": "单次跳变提醒阈值（%）",
    "alert_day_pct": "当日异动提醒阈值（%）",
    "alert_cooldown_min": "提醒冷却（分钟）",
    "fee_rate": "交易行手续费率（%）",
    "max_pages": "全量扫描最大页数",
}

# 已知口径前缀（用于归类，按长度倒序匹配，避免 7.62x51mm 被 7.62 截断）
CALIBER_HINTS = [
    "4.6x30mm", "5.7x28mm", "5.8x42mm", "6.8x51mm", "12.7x55mm", "12.7x108mm",
    "7.62x39mm", "7.62x51mm", "7.62x54R", "5.56x45mm", "5.45x39mm",
    "9x19mm", "9x39mm", "12 Gauge", ".50 AE", ".45 ACP", ".357 Magnum",
    "45-70 Govt", ".300 BLK", ".338 LM", ".300 Win", "箭矢",
]


# --------------------------------------------------------------------------
# 日志
# --------------------------------------------------------------------------
def setup_logging(verbose: bool = False) -> None:
    os.makedirs(DATA_DIR, exist_ok=True)
    root = logging.getLogger()
    root.setLevel(logging.DEBUG if verbose else logging.INFO)
    root.handlers.clear()

    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s", "%Y-%m-%d %H:%M:%S")

    stream = logging.StreamHandler(sys.stdout)
    stream.setFormatter(fmt)
    stream.setLevel(logging.DEBUG if verbose else logging.INFO)
    root.addHandler(stream)

    file_h = RotatingFileHandler(LOG_PATH, maxBytes=2 * 1024 * 1024, backupCount=3, encoding="utf-8")
    file_h.setFormatter(fmt)
    file_h.setLevel(logging.DEBUG)
    root.addHandler(file_h)


log = logging.getLogger("ammo")


# --------------------------------------------------------------------------
# 抓取层
# --------------------------------------------------------------------------
def http_get(url: str, timeout: int = 25, cookie: str | None = None) -> str:
    headers = {
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "zh-CN,zh;q=0.9",
        "Referer": "https://orzice.com/",
    }
    if cookie:
        headers["Cookie"] = cookie
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        raw = resp.read()
        encoding = (resp.headers.get("Content-Encoding") or "").lower()
        if "gzip" in encoding:
            raw = gzip.decompress(raw)
        return raw.decode("utf-8", "replace")


ROW_RE = re.compile(r"<tr>(.*?)</tr>", re.S)
CELL_RE = re.compile(r"<td[^>]*>(.*?)</td>", re.S)
NAME_RE = re.compile(r'<div class="ui-tname">([^<]+)</div>')
INFO_RE = re.compile(r'href="/v/info/(\d+)"')
PIC_RE = re.compile(r'src="([^"]+playerhub[^"]+)"')
GRADE_RE = re.compile(r'data-grade="(\d+)"')
PRICE_RE = re.compile(r'<span class="icon-gold ui-num">(\d+)</span>')
PRICE_RE_ALT = re.compile(r'<div class="ui-num">\s*(\d+)\s*</div>')
LOGIN_WALL_HINT = "登陆查看价格"
NUMFUNC_RE = re.compile(r"NumQfw\((\d+)\)")
PCT_RE = re.compile(r">(-?\d+(?:\.\d+)?)%<")


def classify_caliber(name: str) -> str:
    low = name.lower()
    for c in CALIBER_HINTS:
        if low.startswith(c.lower()) or low.startswith(c.lower().replace(" ", "")):
            return c
    m = re.match(r"([\d.]+(?:x[\d.]*)[a-z]*mm|\d+\s?Gauge|\.\d+\s?[a-z]+)", name, re.I)
    if m:
        return m.group(1).strip()
    if "箭" in name:
        return "箭矢"
    return "其他"


def parse_rows(html: str) -> list[dict]:
    """把页面表格拆成条目。字段缺失时对应值给 None，不抛异常。"""
    out: list[dict] = []
    for row_html in ROW_RE.findall(html):
        name_m = NAME_RE.search(row_html)
        if not name_m:
            continue
        cells = CELL_RE.findall(row_html)
        if len(cells) < 6:          # 表头行 / 异常行直接跳过
            continue
        oid_m = INFO_RE.search(row_html)
        pic_m = PIC_RE.search(row_html)
        grade_m = GRADE_RE.search(row_html)
        price_m = PRICE_RE.search(row_html) or PRICE_RE_ALT.search(row_html)
        hist = [int(x) for x in NUMFUNC_RE.findall(row_html)]
        pcts = [float(x) for x in PCT_RE.findall(row_html)]

        name = name_m.group(1).strip()
        price = int(price_m.group(1)) if price_m else None
        blocked = (LOGIN_WALL_HINT in row_html) and price is None
        # 价格为 0 或缺失通常表示该物品当前不可交易/站点未放开实时价，仍保留记录但标记
        out.append(
            {
                "oid": oid_m.group(1) if oid_m else "",
                "name": name,
                "caliber": classify_caliber(name),
                "grade": int(grade_m.group(1)) if grade_m else 0,
                "pic": pic_m.group(1) if pic_m else "",
                "price": price,
                "blocked": blocked,
                "day_pct": pcts[0] if len(pcts) > 0 else None,
                "d3_price": hist[0] if len(hist) > 0 else None,
                "d3_pct": pcts[1] if len(pcts) > 1 else None,
                "d7_price": hist[1] if len(hist) > 1 else None,
                "d7_pct": pcts[2] if len(pcts) > 2 else None,
                "d30_price": hist[2] if len(hist) > 2 else None,
                "d30_pct": pcts[3] if len(pcts) > 3 else None,
            }
        )
    return out


class SourceError(RuntimeError):
    """数据源取数失败（结构变化、会话失效、限流等）。"""


class SixOwSource:
    """6ow.cc（酸角洲数据站）交易行行情适配器 —— 默认数据源。

    站点前端不是直出 HTML，而是用 HMAC-SHA256 签名请求 /api/act.php：
        canonical = "POST\\n/api/act.php\\n{timestamp}\\n{nonce}\\n{sha256(body)}"
        signature = HMAC-SHA256(bytes.fromhex(request_key), canonical)
    request_key / csrf 来自页面 meta，登录态之外的会话也能用，因此免登录即可
    拿到全量实时价。一次请求返回 1000+ 物品，其中子弹 80+ 种。
    """

    name = "6ow.cc（酸角洲数据站）"
    BASE = "https://6ow.cc"
    PAGE = BASE + "/pages/ammo.php"
    API_PATH = "/api/act.php"

    def __init__(self, gap_ms: int = 1100, cookie: str = ""):
        self.gap_ms = gap_ms
        self.cookie = cookie or ""
        self.key = ""
        self.csrf = ""
        self.offset = 0
        self.boot_at = 0.0
        self._cache: list[dict] = []
        self.market_updated_at: str | None = None
        self.jar = http.cookiejar.CookieJar()
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.jar)
        )

    # -------- 底层签名请求 -------------
    def _post(self, act: str, data: dict | None = None, ctx: bool = False,
              key: str | None = None, csrf: str | None = None) -> dict:
        body = json.dumps(
            {"act": act, "mode": "read", "data": data or {}},
            separators=(",", ":"), ensure_ascii=False,
        )
        ts = str(int(time.time() * 1000) + self.offset)
        nonce = secrets.token_hex(16)
        digest = hashlib.sha256(body.encode("utf-8")).hexdigest()
        canonical = "\n".join(["POST", self.API_PATH, ts, nonce, digest]).encode("utf-8")
        raw_key = key or self.key
        if not raw_key:
            raise SourceError("尚未取得签名 key")
        sig = hmac.new(bytes.fromhex(raw_key), canonical, hashlib.sha256).hexdigest()
        headers = {
            "User-Agent": UA,
            "Content-Type": "application/json",
            "Accept": "application/json, text/plain, */*",
            "Origin": self.BASE,
            "Referer": self.PAGE,
            "X-ND-Timestamp": ts,
            "X-ND-Nonce": nonce,
            "X-ND-Signature": sig,
        }
        if ctx:
            headers["X-ND-Context"] = "1"      # 仅 auth/context 用这个头
        else:
            headers["X-CSRF-Token"] = csrf or self.csrf
        req = urllib.request.Request(
            self.BASE + self.API_PATH, data=body.encode("utf-8"), method="POST", headers=headers
        )
        try:
            with self.opener.open(req, timeout=25) as resp:
                return json.loads(resp.read().decode("utf-8", "replace"))
        except (urllib.error.URLError, json.JSONDecodeError, OSError) as e:
            raise SourceError(f"请求 {act} 失败：{e}") from e

    def _bootstrap(self) -> None:
        """取页面 meta 里的 request-key / csrf，建立带 cookie 的会话。"""
        try:
            req = urllib.request.Request(
                self.PAGE, headers={"User-Agent": UA, "Accept-Language": "zh-CN,zh;q=0.9"}
            )
            html = self.opener.open(req, timeout=25).read().decode("utf-8", "replace")
        except (urllib.error.URLError, OSError) as e:
            raise SourceError(f"打开 6ow 页面失败：{e}") from e
        m_key = re.search(r'name="request-key" content="([^"]+)"', html)
        m_csrf = re.search(r'name="csrf-token" content="([^"]+)"', html)
        if not m_key or not m_csrf:
            raise SourceError("6ow 页面结构已变化：找不到 request-key / csrf-token")
        meta_key, meta_csrf = m_key.group(1), m_csrf.group(1)
        ctx = self._post("auth/context", ctx=True, key=meta_key, csrf=meta_csrf)
        data = ctx.get("data") or {}
        if not ctx.get("ok") or not data.get("request_key"):
            raise SourceError(f"6ow 会话初始化失败：{ctx.get('message') or ctx.get('code')}")
        self.key = data["request_key"]
        self.csrf = data.get("csrf") or meta_csrf
        server_ms = int(data.get("server_time") or 0)
        self.offset = server_ms - int(time.time() * 1000) if server_ms else 0
        self._post("session")
        self.boot_at = time.time()
        log.debug("6ow 会话就绪，时钟偏差 %sms", self.offset)

    def _call(self, act: str, data: dict | None = None, retry: bool = True) -> dict:
        if not self.key or time.time() - self.boot_at > 1800:   # 半小时刷新一次会话
            self._bootstrap()
        res = self._post(act, data)
        if not res.get("ok"):
            if res.get("code") == 419 and retry:
                log.info("6ow 会话过期，重新握手")
                self._bootstrap()
                return self._call(act, data, retry=False)
            raise SourceError(f"6ow 接口 {act} 返回失败：{res.get('message') or res.get('code')}")
        return res

    # ------------- 对外接口 -------------
    def fetch_all(self, max_pages: int = 0) -> tuple[list[dict], int]:
        """一次请求拿全量交易行，过滤出子弹类目。"""
        res = self._call("market")
        data = res.get("data") or {}
        self.market_updated_at = data.get("updated_at")
        rows: list[dict] = []
        for it in data.get("items") or []:
            if (it.get("category") or "") != "ammo":
                continue
            if not it.get("object_id") or not it.get("name"):
                continue
            rows.append(
                {
                    "oid": str(it["object_id"]),
                    "name": it["name"],
                    "caliber": it.get("subcategory") or classify_caliber(it["name"]),
                    "grade": int(it.get("grade") or 0),
                    "pic": it.get("image") or "",
                    "price": to_int(it.get("price")),
                    "day_pct": to_float(it.get("change")),
                    "high": to_int(it.get("high")),
                    "low": to_int(it.get("low")),
                    "d3_price": None, "d3_pct": None,
                    "d7_price": None, "d7_pct": None,
                    "d30_price": None, "d30_pct": None,
                    "blocked": False,
                }
            )
        self._cache = rows
        return rows, 1

    def fetch_by_keyword(self, keyword: str) -> list[dict]:
        """本地过滤最近一次全量结果，避免为关注项再发请求。"""
        if not self._cache:
            self.fetch_all()
        kw = (keyword or "").strip().lower()
        if not kw:
            return []
        return [
            r for r in self._cache
            if kw in r["name"].lower() or kw in (r["caliber"] or "").lower()
        ]


class OrziceSource:
    """orzice 站点采集适配器。想换数据源，只需实现 fetch_all / fetch_by_keyword。

    cookie：站点对未登录访客会隐藏实时价（价格显示为“-”并提示登陆查看）。
    在站点登录后，把浏览器里的 Cookie 串填进 config.json 的 cookie 字段，
    程序就会带上它请求，能拿到实时价。
    """

    name = "orzice.com/v/ammo"

    def __init__(self, gap_ms: int = 1100, cookie: str = ""):
        self.gap_ms = gap_ms
        self.cookie = cookie or ""

    def _sleep(self) -> None:
        time.sleep((self.gap_ms + random.randint(-150, 250)) / 1000.0)

    def fetch_page(self, page: int) -> str:
        return http_get(f"{SOURCE_BASE}?p={page}", cookie=self.cookie)

    def fetch_all(self, max_pages: int) -> tuple[list[dict], int]:
        """翻页抓全量。返回 (条目列表, 实际页数)。"""
        rows: dict[str, dict] = {}
        pages = 0
        for page in range(1, max_pages + 1):
            try:
                html = self.fetch_page(page)
            except urllib.error.HTTPError as e:
                if e.code == 404:      # 翻到头了
                    log.debug("第 %s 页 404，判定为末页", page)
                    break
                raise
            parsed = parse_rows(html)
            if not parsed:
                break
            for r in parsed:
                if r["oid"] and r["oid"] not in rows:
                    rows[r["oid"]] = r
            pages += 1
            self._sleep()
        return list(rows.values()), pages

    def fetch_by_keyword(self, keyword: str) -> list[dict]:
        kw = (keyword or "").strip()[:10]          # 站点限制搜索词 10 字符
        if not kw:
            return []
        html = http_get(f"{SOURCE_BASE}?n={urllib.request.quote(kw)}", cookie=self.cookie)
        return parse_rows(html)


# --------------------------------------------------------------------------
# 指数口径
# --------------------------------------------------------------------------
# 6ow 的 grade 是「品质色档」（白1 绿2 蓝3 紫4 金5），不是穿透等级。
# 实测它与游戏内穿透等级基本一致，唯一例外是 0 级弹：穿透 0 但品质可能是绿/蓝/紫。
# 0 级弹 = 玩家说的「肉弹」（无法穿透任何护甲、肉伤系数最高），单独成板块。
MEAT_KEYS = ("rip", "r37.f", "8.5毫米鹿弹", "龙息", "9号霰射", "govt rn")
PEN_LABEL = {0: "0级·肉弹", 1: "1级弹", 2: "2级弹", 3: "3级弹", 4: "4级弹", 5: "5级弹", 6: "6级弹", 7: "7级弹"}
INDEX_BASE = 1000.0          # 指数起点
INDEX_BUCKET = 900           # 历史序列按 15 分钟分桶


def pen_of(name: str, grade) -> int:
    """穿透等级：命中 0 级白名单的按 0，其余沿用品质档（与图鉴一致）。"""
    n = (name or "").lower()
    if any(k in n for k in MEAT_KEYS):
        return 0
    try:
        g = int(grade or 0)
    except (TypeError, ValueError):
        g = 0
    return min(max(g, 0), 7)


# --------------------------------------------------------------------------
# 数据库
# --------------------------------------------------------------------------
class Store:
    def __init__(self, path: str = DB_PATH):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        self.lock = threading.RLock()
        self.conn = sqlite3.connect(path, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self._init_schema()

    def _init_schema(self) -> None:
        with self.lock, self.conn:
            self.conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS items(
                    oid TEXT PRIMARY KEY,
                    name TEXT NOT NULL,
                    caliber TEXT,
                    grade INTEGER DEFAULT 0,
                    pic TEXT,
                    first_seen INTEGER,
                    last_seen INTEGER,
                    last_price INTEGER,
                    day_pct REAL,
                    d3_price INTEGER, d3_pct REAL,
                    d7_price INTEGER, d7_pct REAL,
                    d30_price INTEGER, d30_pct REAL,
                    high INTEGER, low INTEGER
                );
                CREATE TABLE IF NOT EXISTS prices(
                    oid TEXT, ts INTEGER, price INTEGER, day_pct REAL,
                    PRIMARY KEY(oid, ts)
                );
                CREATE INDEX IF NOT EXISTS idx_prices_oid ON prices(oid, ts);
                CREATE TABLE IF NOT EXISTS watch(
                    oid TEXT PRIMARY KEY,
                    note TEXT,
                    buy_price INTEGER,
                    qty INTEGER DEFAULT 0,
                    alert_below INTEGER,
                    alert_above INTEGER,
                    alert_day_pct REAL,
                    enabled INTEGER DEFAULT 1,
                    created_at INTEGER
                );
                CREATE TABLE IF NOT EXISTS alerts(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts INTEGER, oid TEXT, name TEXT, kind TEXT, level TEXT,
                    message TEXT, price INTEGER
                );
                CREATE INDEX IF NOT EXISTS idx_alerts_ts ON alerts(ts);
                CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT);
                CREATE TABLE IF NOT EXISTS runs(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts INTEGER, mode TEXT, pages INTEGER, items INTEGER,
                    cost_ms INTEGER, ok INTEGER, msg TEXT
                );
                -- 模拟盘：虚拟资金账户 + 持仓 + 成交流水 + 权益曲线
                CREATE TABLE IF NOT EXISTS sim_account(
                    id INTEGER PRIMARY KEY CHECK (id = 1),
                    initial_cash REAL, cash REAL, created_at INTEGER
                );
                CREATE TABLE IF NOT EXISTS sim_positions(
                    oid TEXT PRIMARY KEY,
                    qty INTEGER NOT NULL,
                    cost REAL NOT NULL,          -- 建仓总成本（含买入手续费）
                    opened_at INTEGER
                );
                CREATE TABLE IF NOT EXISTS sim_trades(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts INTEGER, oid TEXT, name TEXT, side TEXT,
                    qty INTEGER, price REAL, fee REAL,
                    cash_delta REAL, pnl REAL    -- 卖出时的已实现盈亏
                );
                CREATE INDEX IF NOT EXISTS idx_sim_trades_ts ON sim_trades(ts);
                CREATE TABLE IF NOT EXISTS sim_equity(
                    ts INTEGER PRIMARY KEY, cash REAL, mv REAL, total REAL
                );
                """
            )
            for k, v in DEFAULT_SETTINGS.items():
                if self.get_setting(k) is None:
                    self.set_setting(k, v)
            for col in ("high", "low"):      # 老库补列，新库已建好
                try:
                    self.conn.execute(f"ALTER TABLE items ADD COLUMN {col} INTEGER")
                except sqlite3.OperationalError:
                    pass
        self._drop_legacy_rows()

    def _drop_legacy_rows(self) -> None:
        """换数据源后清掉旧源留下的小 oid 记录。

        原 orzice 源的物品 id 是 3 位数字（如 612），6ow 源用 11 位 object_id，
        两套 id 无法互通，因此旧记录直接丢弃，避免看板里混着两套数据。
        """
        with self.lock, self.conn:
            legacy = self.conn.execute(
                "SELECT COUNT(*) AS c FROM items WHERE LENGTH(oid) < 8"
            ).fetchone()["c"]
            if not legacy:
                return
            for table in ("items", "prices", "watch", "alerts"):
                self.conn.execute(f"DELETE FROM {table} WHERE LENGTH(oid) < 8")
            log.warning("检测到旧数据源记录 %s 条，已清理", legacy)

    # ------- settings -------
    def get_setting(self, k: str):
        row = self.conn.execute("SELECT v FROM settings WHERE k=?", (k,)).fetchone()
        if row is None:
            return None
        try:
            return json.loads(row["v"])
        except (json.JSONDecodeError, TypeError):
            return row["v"]

    def set_setting(self, k: str, v) -> None:
        with self.lock, self.conn:
            self.conn.execute(
                "INSERT INTO settings(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v",
                (k, json.dumps(v, ensure_ascii=False)),
            )

    def all_settings(self) -> dict:
        with self.lock:
            rows = self.conn.execute("SELECT k,v FROM settings").fetchall()
        out = dict(DEFAULT_SETTINGS)
        for r in rows:
            try:
                out[r["k"]] = json.loads(r["v"])
            except (json.JSONDecodeError, TypeError):
                out[r["k"]] = r["v"]
        return out

    # ------- 行情写入 -------
    def upsert_items(self, rows: list[dict], ts: int) -> None:
        """写入最新行情，并按规则压缩历史点。"""
        with self.lock, self.conn:
            for r in rows:
                prev = self.conn.execute(
                    "SELECT last_price, last_seen FROM items WHERE oid=?", (r["oid"],)
                ).fetchone()
                self.conn.execute(
                    """
                    INSERT INTO items(oid,name,caliber,grade,pic,first_seen,last_seen,last_price,
                                      day_pct,d3_price,d3_pct,d7_price,d7_pct,d30_price,d30_pct,
                                      high,low)
                    VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                    ON CONFLICT(oid) DO UPDATE SET
                        name=excluded.name, caliber=excluded.caliber, grade=excluded.grade,
                        pic=excluded.pic, last_seen=excluded.last_seen,
                        -- 拿不到实时价时（站点登录墙/限流会返回"-"）保留上一次的观测值，不能覆盖成 NULL
                        last_price=COALESCE(excluded.last_price, items.last_price),
                        day_pct=COALESCE(excluded.day_pct, items.day_pct),
                        d3_price=COALESCE(excluded.d3_price, items.d3_price),
                        d3_pct=COALESCE(excluded.d3_pct, items.d3_pct),
                        d7_price=COALESCE(excluded.d7_price, items.d7_price),
                        d7_pct=COALESCE(excluded.d7_pct, items.d7_pct),
                        d30_price=COALESCE(excluded.d30_price, items.d30_price),
                        d30_pct=COALESCE(excluded.d30_pct, items.d30_pct),
                        high=COALESCE(excluded.high, items.high),
                        low=COALESCE(excluded.low, items.low)
                    """,
                    (
                        r["oid"], r["name"], r["caliber"], r["grade"], r["pic"], ts, ts,
                        r["price"], r["day_pct"], r["d3_price"], r["d3_pct"],
                        r["d7_price"], r["d7_pct"], r["d30_price"], r["d30_pct"],
                        r.get("high"), r.get("low"),
                    ),
                )
                if r["price"] is None:
                    continue
                # 历史点压缩：价格没变且最近一条记录不足 20 分钟，就不再写点
                last = self.conn.execute(
                    "SELECT ts, price FROM prices WHERE oid=? ORDER BY ts DESC LIMIT 1", (r["oid"],)
                ).fetchone()
                if not (last and last["price"] == r["price"] and ts - last["ts"] < 1200):
                    self.conn.execute(
                        "INSERT OR REPLACE INTO prices(oid,ts,price,day_pct) VALUES(?,?,?,?)",
                        (r["oid"], ts, r["price"], r["day_pct"]),
                    )
                self._seed_history(r, ts)      # 补种与压缩无关，任何一轮都尝试（内部幂等）

    def _seed_history(self, r: dict, ts: int) -> None:
        """首次见到某物品时，用来源自带的 30/7/3 日价补几个粗粒度历史点，避免曲线空着。

        这几个点是"参考点"而非本程序实测点，当本地实测点攒够两个后就不再补。
        """
        row = self.conn.execute(
            "SELECT COUNT(*) AS c FROM prices WHERE oid=?", (r["oid"],)
        ).fetchone()
        if row and row["c"] >= 2:
            return
        # 有当日涨跌但没有历史点时，用涨跌幅反推"昨日价"，让曲线至少有两点
        prev = r.get("prev_price")
        if not prev and r.get("price") and r.get("day_pct") not in (None, -100):
            try:
                prev = int(round(r["price"] / (1 + float(r["day_pct"]) / 100.0)))
            except (TypeError, ValueError, ZeroDivisionError):
                prev = None
        if prev:
            self.conn.execute(
                "INSERT OR REPLACE INTO prices(oid,ts,price,day_pct) VALUES(?,?,?,?)",
                (r["oid"], ts - 86400, int(prev), None),
            )
        for days, key in ((30, "d30_price"), (7, "d7_price"), (3, "d3_price")):
            v = r.get(key)
            if not v:
                continue
            self.conn.execute(
                "INSERT OR REPLACE INTO prices(oid,ts,price,day_pct) VALUES(?,?,?,?)",
                (r["oid"], ts - days * 86400, int(v), None),
            )

    def previous_price(self, oid: str, before_ts: int | None = None, window: int = 1800) -> int | None:
        """取上一轮扫描价：只看 before_ts 之前 30 分钟内的点。

        限定窗口是为了避开补种的历史参考点（3/7/30 天前），否则会被误判成"单次跳变"。
        """
        ts_limit = before_ts if before_ts is not None else int(time.time())
        with self.lock:
            row = self.conn.execute(
                "SELECT price FROM prices WHERE oid=? AND ts < ? AND ts >= ? ORDER BY ts DESC LIMIT 1",
                (oid, ts_limit, ts_limit - window),
            ).fetchone()
        return row["price"] if row else None

    def history(self, oid: str, limit: int = 120) -> list[list[int]]:
        with self.lock:
            rows = self.conn.execute(
                "SELECT ts, price FROM prices WHERE oid=? ORDER BY ts DESC LIMIT ?", (oid, limit)
            ).fetchall()
        return [[r["ts"], r["price"]] for r in reversed(rows)]

    def items_overview(self, spark_points: int = 30) -> list[dict]:
        with self.lock:
            items = self.conn.execute("SELECT * FROM items ORDER BY last_price DESC").fetchall()
            watch_rows = {r["oid"]: dict(r) for r in self.conn.execute("SELECT * FROM watch").fetchall()}
        out = []
        for it in items:
            d = dict(it)
            d["pen"] = pen_of(it["name"], it["grade"])
            w = watch_rows.get(it["oid"])
            d["watch"] = bool(w)
            d["w"] = w
            d["spark"] = [p for _, p in self.history(it["oid"], spark_points)]
            out.append(d)
        return out

    # -------- 大盘 / 板块指数 --------
    def index_state(self, max_points: int = 60, cache_sec: int = 30) -> dict:
        """等权涨跌幅指数：每种子弹以「本地最早价」为基期，指数 = 1000×(1+平均涨跌幅)。

        6ow 不提供昨收价，所以不能用市值加权或昨收口径；用各自基期做等权，
        好处是不同口径、不同价位的子弹不会被 7000 币的 7.62x51 带偏。
        """
        now = int(time.time())
        cached = getattr(self, "_idx_cache", None)
        if cached and now - cached[0] < cache_sec:
            return cached[1]

        with self.lock:
            items = [dict(r) for r in self.conn.execute(
                "SELECT oid,name,grade,last_price,day_pct,caliber FROM items "
                "WHERE last_price IS NOT NULL ORDER BY grade, name"
            ).fetchall()]
            base_rows = self.conn.execute(
                "SELECT p.oid AS oid, p.price AS price FROM prices p "
                "JOIN (SELECT oid, MIN(ts) AS mt FROM prices GROUP BY oid) m "
                "ON m.oid = p.oid AND m.mt = p.ts"
            ).fetchall()
            bases = {r["oid"]: r["price"] for r in base_rows}
            hist = self.conn.execute(
                "SELECT oid, ts, price FROM prices WHERE price IS NOT NULL ORDER BY ts"
            ).fetchall()

        groups: dict[str, list[dict]] = {}
        for it in items:
            pen = pen_of(it["name"], it["grade"])
            it["pen"] = pen
            groups.setdefault(f"P{pen}", []).append(it)

        def agg(members: list[dict], price_map: dict) -> dict:
            chgs: list[float] = []
            up = down = 0
            for it in members:
                p = price_map.get(it["oid"])
                b = bases.get(it["oid"])
                if not p or not b:
                    continue
                chg = (p / b - 1.0) * 100.0
                chgs.append(chg)
                if chg > 0.01:
                    up += 1
                elif chg < -0.01:
                    down += 1
            avg = sum(chgs) / len(chgs) if chgs else 0.0
            return {
                "value": INDEX_BASE * (1.0 + avg / 100.0),
                "chg": avg,
                "cnt": len(chgs),
                "up": up,
                "down": down,
                "flat": len(chgs) - up - down,
            }

        cur = {it["oid"]: it["last_price"] for it in items}
        order = [f"P{g}" for g in sorted(PEN_LABEL) if f"P{g}" in groups]
        label = {f"P{g}": v for g, v in PEN_LABEL.items()}

        sectors = []
        for key in order:
            m = agg(groups.get(key) or [], cur)
            m.update({"key": key, "name": label.get(key, key)})
            sectors.append(m)
        market = agg(items, cur)
        market.update({"key": "market", "name": "大盘"})

        # 历史序列：按时间桶聚合，桶内取各子弹最后成交价，缺价的子弹沿用前值
        ts_map: dict[int, dict[str, int]] = {}
        for r in hist:
            ts_map.setdefault(int(r["ts"]), {})[r["oid"]] = int(r["price"])
        keys = ["market"] + order
        series: dict[str, list[list]] = {k: [] for k in keys}      # 全历史分时（15 分钟一点）
        today: dict[str, list[list]] = {k: [] for k in keys}       # 今日分时
        candles: dict[str, list[list]] = {k: [] for k in keys}     # 15 分钟 K（备用）
        # 日 / 周 / 月 / 年 K：同一周期内多次采样累积成 开/高/低/收
        PERIODS = ("day", "week", "month", "year")
        kl: dict[str, dict[str, dict[int, list]]] = {
            p: {k: {} for k in keys} for p in PERIODS
        }
        running: dict[str, int] = {}
        lt_now = time.localtime(now)
        today0 = int(time.mktime((lt_now.tm_year, lt_now.tm_mon, lt_now.tm_mday, 0, 0, 0, 0, 0, -1)))

        def period_starts(ts: int) -> dict[str, int]:
            lt = time.localtime(ts)
            day0 = int(time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0, 0, 0, -1)))
            return {
                "day": day0,
                "week": day0 - lt.tm_wday * 86400,          # 本周一 00:00
                "month": int(time.mktime((lt.tm_year, lt.tm_mon, 1, 0, 0, 0, 0, 0, -1))),
                "year": int(time.mktime((lt.tm_year, 1, 1, 0, 0, 0, 0, 0, -1))),
            }

        # 早期扫描覆盖的子弹少，指数点会假跳（1000 直接拉到 1040），
        # 只保留覆盖六成以上成分的桶，曲线才是可信的市场走势。
        min_cover = max(3, int(len(items) * 0.6))
        for ts in sorted(ts_map):
            running.update(ts_map[ts])
            if len(running) < min_cover:
                continue
            bk = (ts // INDEX_BUCKET) * INDEX_BUCKET
            starts = period_starts(ts)
            for key in keys:
                members = items if key == "market" else (groups.get(key) or [])
                v = round(agg(members, running)["value"], 2)
                # 分时：同一 15 分钟桶内保留最后一次采样
                line = series[key]
                if line and line[-1][0] == bk:
                    line[-1][1] = v
                else:
                    line.append([bk, v])
                if bk >= today0:
                    t = today[key]
                    if t and t[-1][0] == bk:
                        t[-1][1] = v
                    else:
                        t.append([bk, v])
                # 15 分钟 K（保留兼容）
                cd = candles[key]
                if cd and cd[-1][0] == bk:
                    c = cd[-1]
                    if v > c[2]:
                        c[2] = v
                    if v < c[3]:
                        c[3] = v
                    c[4] = v
                else:
                    cd.append([bk, v, v, v, v])
                # 日/周/月/年 K
                for p in PERIODS:
                    ps = starts[p]
                    row = kl[p][key].get(ps)
                    if row is None:
                        kl[p][key][ps] = [ps, v, v, v, v]
                    else:
                        if v > row[2]:
                            row[2] = v
                        if v < row[3]:
                            row[3] = v
                        row[4] = v

        def downsample(pts: list, n: int = max_points) -> list:
            if len(pts) <= n:
                return pts
            step = len(pts) / float(n)
            out = [pts[min(len(pts) - 1, int(i * step))] for i in range(n)]
            out[-1] = pts[-1]
            return out

        series = {k: downsample(v) for k, v in series.items()}
        today = {k: downsample(v) for k, v in today.items()}
        candles = {k: downsample(v) for k, v in candles.items()}
        kline = {
            p: {k: [row for _, row in sorted(kv.items())] for k, kv in kv_map.items()}
            for p, kv_map in kl.items()
        }

        ranked = []
        for it in items:
            b, p = bases.get(it["oid"]), it["last_price"]
            if not b or not p:
                continue
            ranked.append({
                "oid": it["oid"], "name": it["name"], "grade": it["grade"],
                "pen": it["pen"], "price": p, "chg": (p / b - 1.0) * 100.0,
            })
        ranked.sort(key=lambda x: x["chg"], reverse=True)

        def rank_block(key: str, top: int = 6) -> dict:
            """单个板块（或大盘）内部的领涨 / 领跌，成分与指数口径一致。"""
            sub = ranked if key == "market" else [r for r in ranked if r["pen"] == int(key[1:])]
            return {
                "leaders": sub[:top],
                "laggers": list(reversed(sub[-top:])) if sub else [],
                "cnt": len(sub),
            }

        ranks = {k: rank_block(k) for k in ["market"] + order}

        payload = {
            "ts": now,
            "count": len(items),
            "base_note": "基期=每种子弹本地首个记录价",
            "market": market,
            "sectors": sectors,
            "series": series,
            "today": today,
            "kline": kline,
            "candles": candles,
            "ranks": ranks,
            "leaders": ranks["market"]["leaders"],
            "laggers": ranks["market"]["laggers"],
            "meat_rule": "0级弹（穿透等级0，无法穿透任何护甲）= 肉弹：RIP / CT / 龙息 / 8.5毫米鹿弹 / 45-70 RN / R37.F / 9号霰射鼠弹",
        }
        self._idx_cache = (now, payload)
        return payload

    def recent_alerts(self, limit: int = 30) -> list[dict]:
        with self.lock:
            rows = self.conn.execute(
                "SELECT * FROM alerts ORDER BY id DESC LIMIT ?", (limit,)
            ).fetchall()
        return [dict(r) for r in rows]

    def last_alert_age(self, oid: str, kind: str) -> int | None:
        with self.lock:
            row = self.conn.execute(
                "SELECT ts FROM alerts WHERE oid=? AND kind=? ORDER BY id DESC LIMIT 1", (oid, kind)
            ).fetchone()
        return int(time.time()) - row["ts"] if row else None

    def add_alert(self, oid: str, name: str, kind: str, level: str, message: str, price: int | None) -> None:
        with self.lock, self.conn:
            self.conn.execute(
                "INSERT INTO alerts(ts,oid,name,kind,level,message,price) VALUES(?,?,?,?,?,?,?)",
                (int(time.time()), oid, name, kind, level, message, price),
            )

    def log_run(self, mode: str, pages: int, items: int, cost_ms: int, ok: bool, msg: str) -> None:
        with self.lock, self.conn:
            self.conn.execute(
                "INSERT INTO runs(ts,mode,pages,items,cost_ms,ok,msg) VALUES(?,?,?,?,?,?,?)",
                (int(time.time()), mode, pages, items, cost_ms, 1 if ok else 0, msg),
            )

    def last_run(self) -> dict | None:
        with self.lock:
            row = self.conn.execute("SELECT * FROM runs ORDER BY id DESC LIMIT 1").fetchone()
        return dict(row) if row else None

    # ------- 关注清单 -------
    def watch_list(self) -> list[dict]:
        with self.lock:
            rows = self.conn.execute("SELECT * FROM watch ORDER BY created_at").fetchall()
        return [dict(r) for r in rows]

    def watch_upsert(self, payload: dict) -> None:
        oid = str(payload.get("oid", "")).strip()
        if not oid:
            raise ValueError("缺少物品 ID")
        fields = {
            "note": payload.get("note", ""),
            "buy_price": to_int(payload.get("buy_price")),
            "qty": to_int(payload.get("qty")) or 0,
            "alert_below": to_int(payload.get("alert_below")),
            "alert_above": to_int(payload.get("alert_above")),
            "alert_day_pct": to_float(payload.get("alert_day_pct")),
            "enabled": 0 if payload.get("enabled") in (0, False, "0", "false") else 1,
        }
        with self.lock, self.conn:
            exists = self.conn.execute("SELECT oid FROM watch WHERE oid=?", (oid,)).fetchone()
            if exists:
                self.conn.execute(
                    """UPDATE watch SET note=?,buy_price=?,qty=?,alert_below=?,alert_above=?,
                                      alert_day_pct=?,enabled=? WHERE oid=?""",
                    (
                        fields["note"], fields["buy_price"], fields["qty"], fields["alert_below"],
                        fields["alert_above"], fields["alert_day_pct"], fields["enabled"], oid,
                    ),
                )
            else:
                self.conn.execute(
                    """INSERT INTO watch(oid,note,buy_price,qty,alert_below,alert_above,
                                        alert_day_pct,enabled,created_at)
                       VALUES(?,?,?,?,?,?,?,?,?)""",
                    (
                        oid, fields["note"], fields["buy_price"], fields["qty"], fields["alert_below"],
                        fields["alert_above"], fields["alert_day_pct"], fields["enabled"], int(time.time()),
                    ),
                )

    def watch_remove(self, oid: str) -> None:
        with self.lock, self.conn:
            self.conn.execute("DELETE FROM watch WHERE oid=?", (oid,))

    # ------- 模拟盘 -------
    """模拟盘规则（和游戏内交易行一致）：

    * 买入：按当前实时价成交，另付手续费（费率取设置的 fee_rate，默认 5%）
    * 卖出：按当前实时价成交，扣同费率手续费，差价计入已实现盈亏
    * 持仓成本用加权平均，卖出不改变剩余持仓的单位成本
    * 总资产 = 现金 + 持仓市值，收益率 = (总资产 - 初始资金) / 初始资金
    """

    def _ensure_account(self) -> dict:
        row = self.conn.execute("SELECT * FROM sim_account WHERE id=1").fetchone()
        if row is None:
            init = float(DEFAULT_SETTINGS.get("sim_initial_cash") or 1000000)
            with self.conn:
                self.conn.execute(
                    "INSERT OR IGNORE INTO sim_account(id,initial_cash,cash,created_at) VALUES(1,?,?,?)",
                    (init, init, int(time.time())),
                )
            row = self.conn.execute("SELECT * FROM sim_account WHERE id=1").fetchone()
        return dict(row)

    def sim_state(self, trade_limit: int = 30) -> dict:
        settings = self.all_settings()
        buy_fee = float(settings.get("sim_buy_fee_pct") or 0.0)
        sell_fee = float(settings.get("sim_sell_fee_pct") or 15.0)
        with self.lock:
            acct = self._ensure_account()
            pos_rows = [dict(r) for r in self.conn.execute("SELECT * FROM sim_positions").fetchall()]
            item_map = {
                r["oid"]: dict(r)
                for r in self.conn.execute("SELECT * FROM items").fetchall()
            }
            trades = [
                dict(r)
                for r in self.conn.execute(
                    "SELECT * FROM sim_trades ORDER BY id DESC LIMIT ?", (trade_limit,)
                ).fetchall()
            ] if trade_limit > 0 else []
            realized = self.conn.execute(
                "SELECT COALESCE(SUM(pnl),0) AS s FROM sim_trades WHERE pnl IS NOT NULL"
            ).fetchone()["s"]
            eq_rows = self.conn.execute(
                "SELECT ts,total FROM sim_equity ORDER BY ts DESC LIMIT 200"
            ).fetchall()

        positions = []
        for p in pos_rows:
            it = item_map.get(p["oid"]) or {}
            price = it.get("last_price")
            qty = int(p["qty"] or 0)
            cost = float(p["cost"] or 0)
            avg = cost / qty if qty else 0.0
            mv = float(price) * qty if price else 0.0
            pnl = mv - cost if price else None
            positions.append(
                {
                    "oid": p["oid"],
                    "name": it.get("name") or p["oid"],
                    "pic": it.get("pic") or "",
                    "grade": it.get("grade") or 0,
                    "qty": qty,
                    "avg_cost": round(avg, 2),
                    "price": price,
                    "market_value": round(mv, 2),
                    "cost": round(cost, 2),
                    "pnl": round(pnl, 2) if pnl is not None else None,
                    "pnl_pct": round(pnl / cost * 100, 2) if pnl is not None and cost else None,
                    "day_pct": it.get("day_pct"),
                    "opened_at": p["opened_at"],
                }
            )
        positions.sort(key=lambda x: -(x["market_value"] or 0))

        mv_total = sum(p["market_value"] for p in positions)
        cost_total = sum(p["cost"] for p in positions)
        cash = float(acct["cash"])
        total = cash + mv_total
        initial = float(acct["initial_cash"] or 0)
        return {
            "initial_cash": round(initial, 2),
            "cash": round(cash, 2),
            "market_value": round(mv_total, 2),
            "cost_total": round(cost_total, 2),
            "unrealized": round(mv_total - cost_total, 2),
            "realized": round(float(realized), 2),
            "total": round(total, 2),
            "roi": round((total - initial) / initial * 100, 2) if initial else 0.0,
            "float_roi": round((mv_total - cost_total) / cost_total * 100, 2) if cost_total else 0.0,
            "positions": positions,
            "trades": trades,
            "equity": [[r["ts"], round(r["total"], 2)] for r in reversed(eq_rows)],
            "buy_fee_pct": buy_fee,
            "sell_fee_pct": sell_fee,
        }

    def sim_buy(self, oid: str, qty) -> dict:
        qty = to_int(qty)
        if not qty or qty <= 0:
            raise ValueError("买入数量必须大于 0")
        settings = self.all_settings()
        fee_rate = float(settings.get("sim_buy_fee_pct") or 0.0)
        with self.lock:
            item = self.conn.execute("SELECT * FROM items WHERE oid=?", (str(oid),)).fetchone()
            if not item or item["last_price"] is None:
                raise ValueError("这个子弹还没有实时价，等下一轮扫描后再买")
            price = float(item["last_price"])
            acct = self._ensure_account()
            gross = price * qty
            fee = round(gross * fee_rate / 100.0, 2)
            need = round(gross + fee, 2)
            if acct["cash"] + 1e-6 < need:
                raise ValueError(f"现金不足：需要 {need:,.0f} 元，可用 {acct['cash']:,.0f} 元")
            with self.conn:
                self.conn.execute("UPDATE sim_account SET cash = cash - ? WHERE id=1", (need,))
                pos = self.conn.execute("SELECT * FROM sim_positions WHERE oid=?", (str(oid),)).fetchone()
                if pos:
                    self.conn.execute(
                        "UPDATE sim_positions SET qty = qty + ?, cost = cost + ? WHERE oid=?",
                        (qty, need, str(oid)),
                    )
                else:
                    self.conn.execute(
                        "INSERT INTO sim_positions(oid,qty,cost,opened_at) VALUES(?,?,?,?)",
                        (str(oid), qty, need, int(time.time())),
                    )
                self.conn.execute(
                    "INSERT INTO sim_trades(ts,oid,name,side,qty,price,fee,cash_delta,pnl)"
                    " VALUES(?,?,?,?,?,?,?,?,NULL)",
                    (int(time.time()), str(oid), item["name"], "buy", qty, price, fee, -need),
                )
        self.sim_snapshot(int(time.time()))     # 成交即记一个权益点，曲线立刻有起点
        return self.sim_state()

    def sim_sell(self, oid: str, qty) -> dict:
        qty = to_int(qty)
        if not qty or qty <= 0:
            raise ValueError("卖出数量必须大于 0")
        settings = self.all_settings()
        fee_rate = float(settings.get("sim_sell_fee_pct") or 15.0)
        with self.lock:
            pos = self.conn.execute("SELECT * FROM sim_positions WHERE oid=?", (str(oid),)).fetchone()
            if pos is None:
                raise ValueError("没有这个子弹的持仓")
            if qty > pos["qty"]:
                raise ValueError(f"持仓不足：只有 {pos['qty']} 发")
            item = self.conn.execute("SELECT * FROM items WHERE oid=?", (str(oid),)).fetchone()
            if not item or item["last_price"] is None:
                raise ValueError("这个子弹还没有实时价，暂时无法卖出")
            price = float(item["last_price"])
            gross = price * qty
            fee = round(gross * fee_rate / 100.0, 2)
            net = round(gross - fee, 2)
            avg = pos["cost"] / pos["qty"]
            pnl = round(net - avg * qty, 2)
            with self.conn:
                self.conn.execute("UPDATE sim_account SET cash = cash + ? WHERE id=1", (net,))
                if qty >= pos["qty"]:
                    self.conn.execute("DELETE FROM sim_positions WHERE oid=?", (str(oid),))
                else:
                    self.conn.execute(
                        "UPDATE sim_positions SET qty = qty - ?, cost = cost - ? WHERE oid=?",
                        (qty, avg * qty, str(oid)),
                    )
                self.conn.execute(
                    "INSERT INTO sim_trades(ts,oid,name,side,qty,price,fee,cash_delta,pnl)"
                    " VALUES(?,?,?,?,?,?,?,?,?)",
                    (int(time.time()), str(oid), item["name"], "sell", qty, price, fee, net, pnl),
                )
        self.sim_snapshot(int(time.time()))
        return self.sim_state()

    def sim_reset(self, initial_cash=None) -> dict:
        init = float(initial_cash or DEFAULT_SETTINGS.get("sim_initial_cash") or 1000000)
        if init <= 0:
            raise ValueError("初始资金必须大于 0")
        with self.lock, self.conn:
            self.conn.execute("DELETE FROM sim_positions")
            self.conn.execute("DELETE FROM sim_trades")
            self.conn.execute("DELETE FROM sim_equity")
            self.conn.execute(
                "INSERT INTO sim_account(id,initial_cash,cash,created_at) VALUES(1,?,?,?)"
                " ON CONFLICT(id) DO UPDATE SET initial_cash=excluded.initial_cash,"
                " cash=excluded.cash, created_at=excluded.created_at",
                (init, init, int(time.time())),
            )
        return self.sim_state()

    def sim_snapshot(self, ts: int) -> None:
        """把某一时刻的账户权益落一条曲线点，用于画收益曲线。"""
        with self.lock, self.conn:
            acct = self.conn.execute("SELECT cash FROM sim_account WHERE id=1").fetchone()
            if acct is None:
                return
            mv = self.conn.execute(
                "SELECT COALESCE(SUM(i.last_price * p.qty), 0) AS mv"
                " FROM sim_positions p JOIN items i ON i.oid = p.oid"
                " WHERE i.last_price IS NOT NULL"
            ).fetchone()["mv"]
            self.conn.execute(
                "INSERT OR REPLACE INTO sim_equity(ts,cash,mv,total) VALUES(?,?,?,?)",
                (ts, acct["cash"], mv, acct["cash"] + mv),
            )


def to_int(v):
    if v is None or v == "":
        return None
    try:
        return int(float(v))
    except (TypeError, ValueError):
        return None


def to_float(v):
    if v is None or v == "":
        return None
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


# --------------------------------------------------------------------------
# 监控引擎
# --------------------------------------------------------------------------
class Monitor:
    def __init__(self, store: Store):
        self.store = store
        self.source = SixOwSource(
            gap_ms=int(store.get_setting("request_gap_ms") or 1100),
            cookie=str(store.get_setting("cookie") or ""),
        )
        self.state = {
            "running": False,
            "mode": None,
            "last_scan_ts": None,
            "last_scan_started": None,
            "scan_cost_ms": None,
            "pages": 0,
            "items": 0,
            "priced": 0,
            "blocked": 0,
            "ok": True,
            "error": None,
            "next_scan_ts": None,
            "backoff_level": 0,
            "full_items": 0,
            "full_pages": 0,
        }
        self.wake = threading.Event()
        self.stop_flag = threading.Event()
        self.thread: threading.Thread | None = None
        self.backoff_level = 0

    # -------- 扫描 --------
    def _check_alerts(self, rows: list[dict], ts: int) -> None:
        s = self.store.all_settings()
        jump_pct = float(s.get("alert_jump_pct") or 3.0)
        day_pct_th = float(s.get("alert_day_pct") or 8.0)
        cooldown = int(s.get("alert_cooldown_min") or 30) * 60
        watches = {w["oid"]: w for w in self.store.watch_list()}

        for r in rows:
            oid, price = r["oid"], r["price"]
            if not oid or price is None:
                continue
            w = watches.get(oid)
            if w and not w["enabled"]:
                continue

            candidates: list[tuple[str, str, str]] = []
            prev = self.store.previous_price(oid, ts)
            # 单次跳变只对"关注项"提醒：全市场 80+ 种都提醒会把人淹掉，
            # 页面上有涨跌列和走势可以直接看。
            if w and prev and prev > 0:
                chg = (price - prev) / prev * 100.0
                if abs(chg) >= jump_pct:
                    arrow = "↑" if chg > 0 else "↓"
                    candidates.append(
                        ("jump", "warn", f"{r['name']} 单次{arrow}{abs(chg):.2f}%：{prev} → {price}")
                    )
            if w:
                if w["alert_below"] and price <= w["alert_below"]:
                    candidates.append(
                        ("below", "buy", f"{r['name']} 跌破买价 {w['alert_below']}，现价 {price}")
                    )
                if w["alert_above"] and price >= w["alert_above"]:
                    candidates.append(
                        ("above", "sell", f"{r['name']} 达到卖价 {w['alert_above']}，现价 {price}")
                    )
                th = w["alert_day_pct"] or day_pct_th
                if r["day_pct"] is not None and th and abs(r["day_pct"]) >= th:
                    direction = "涨" if r["day_pct"] > 0 else "跌"
                    candidates.append(
                        ("momentum", "warn",
                         f"{r['name']} 较今日低点{direction} {abs(r['day_pct']):.2f}%，现价 {price}")
                    )

            for kind, level, msg in candidates:
                age = self.store.last_alert_age(oid, kind)
                if age is not None and age < cooldown:
                    continue
                self.store.add_alert(oid, r["name"], kind, level, msg, price)
                log.info("提醒 [%s] %s", kind, msg)

    def scan(self, mode: str = "full", keywords: list[str] | None = None) -> dict:
        t0 = time.time()
        started = int(t0)
        self.state.update(
            running=True, mode=mode, last_scan_started=started, error=None, ok=True, next_scan_ts=None
        )
        settings = self.store.all_settings()
        self.source.gap_ms = int(settings.get("request_gap_ms") or 1100)
        self.source.cookie = str(settings.get("cookie") or "")
        rows: list[dict] = []
        pages = 0
        try:
            if mode == "watch" and keywords:
                # 6ow 一次请求就返回全量行情，快刷不必按口径逐条搜，直接筛关注项
                all_rows, _ = self.source.fetch_all(0)
                woids = {w["oid"] for w in self.store.watch_list() if w["enabled"]}
                rows = [r for r in all_rows if r["oid"] in woids] if woids else all_rows
                pages = 1
            else:
                rows, pages = self.source.fetch_all(int(settings.get("max_pages") or 14))

            ts = int(time.time())
            if not rows:
                raise RuntimeError("抓取结果为空，站点结构可能已变化")

            priced = sum(1 for r in rows if r.get("price") is not None)
            blocked = sum(1 for r in rows if r.get("blocked"))
            self.store.upsert_items(rows, ts)      # 能拿到多少写多少，缺失字段保留旧值
            if priced:
                self._check_alerts(rows, ts)
            self.store.sim_snapshot(ts)            # 模拟盘权益曲线点

            cost = int((time.time() - t0) * 1000)
            degraded = priced == 0
            err_msg = None
            if degraded:
                err_msg = (
                    "站点对未登录访客隐藏了实时价（或触发了限流），本次保留上一次观测价；"
                    "可在 config.json 里填 cookie，或稍后自动重试"
                )
            update = dict(
                running=False,
                last_scan_ts=ts,
                scan_cost_ms=cost,
                pages=pages,
                items=len(rows),
                priced=priced,
                blocked=blocked,
                ok=not degraded,
                error=err_msg,
                mode=mode,
            )
            if mode == "full":      # 快刷只覆盖局部，全量统计单独留一份，避免看板数字跳动
                update["full_items"] = len(rows)
                update["full_pages"] = pages
            self.state.update(update)   # type: ignore[arg-type]
            self.store.log_run(mode, pages, len(rows), cost, not degraded, err_msg or "")
            log.info(
                "扫描完成 mode=%s pages=%s items=%s priced=%s cost=%sms",
                mode, pages, len(rows), priced, cost,
            )
            return {
                "ok": not degraded, "items": len(rows), "pages": pages,
                "cost_ms": cost, "priced": priced, "blocked": blocked, "error": err_msg,
            }
        except Exception as e:
            cost = int((time.time() - t0) * 1000)
            self.state.update(running=False, ok=False, error=str(e), scan_cost_ms=cost)
            self.store.log_run(mode, pages, len(rows), cost, False, str(e))
            log.error("扫描失败：%s", e)
            return {"ok": False, "error": str(e)}

    # -------- 调度 --------
    def _watch_keywords(self) -> list[str]:
        """关注物品按口径归并成搜索词，一次请求覆盖同口径多个子弹。"""
        items = {i["oid"]: i for i in self.store.items_overview(spark_points=0)}
        kws: dict[str, int] = {}
        for w in self.store.watch_list():
            if not w["enabled"]:
                continue
            item = items.get(w["oid"])
            if not item:
                continue
            kw = (item.get("caliber") or item["name"])[:10]
            if kw:
                kws[kw] = kws.get(kw, 0) + 1
        return sorted(kws, key=lambda k: -kws[k])[:12]

    def loop(self) -> None:
        log.info("调度线程启动")
        next_full = time.time()          # 启动立刻全量扫一次
        while not self.stop_flag.is_set():
            now = time.time()
            settings = self.store.all_settings()
            full_gap = max(60, int(settings.get("full_scan_interval") or 300))
            watch_gap = max(30, int(settings.get("watch_interval") or 60))

            if now >= next_full:
                res = self.scan("full")
                # 数据源降级（登录墙 / 限流）时指数退避，别继续给对方加压
                self.backoff_level = 0 if res.get("ok") else min(self.backoff_level + 1, 3)
                next_full = time.time() + full_gap * (2 ** self.backoff_level)
                self.state["next_scan_ts"] = int(next_full)
                self.state["backoff_level"] = self.backoff_level
                self.wake.wait(5)
                self.wake.clear()
                continue

            if self.backoff_level == 0:          # 降级期间不做关注快刷
                kws = self._watch_keywords()
                if kws and watch_gap < full_gap:
                    self.scan("watch", kws)

            self.state["next_scan_ts"] = int(next_full)
            self.wake.wait(max(5, min(watch_gap, int(next_full - time.time()))))
            self.wake.clear()

        log.info("调度线程退出")

    def start(self) -> None:
        self.thread = threading.Thread(target=self.loop, name="monitor-loop", daemon=True)
        self.thread.start()

    def stop(self) -> None:
        self.stop_flag.set()
        self.wake.set()

    def status(self) -> dict:
        s = dict(self.state)
        s["server_time"] = int(time.time())
        return s


# --------------------------------------------------------------------------
# HTTP 服务
# --------------------------------------------------------------------------
LOGIN_HTML = """<!DOCTYPE html>
<html lang="zh-CN"><head>
<meta charset="utf-8" /><meta name="viewport" content="width=device-width, initial-scale=1" />
<title>访问口令</title>
<style>
  :root{--bg:#0b0e11;--panel:#141a1f;--line:#222b33;--text:#dfe6ec;--muted:#7d8a95;--gold:#d9b25f;}
  *{box-sizing:border-box;}
  body{margin:0;min-height:100vh;display:grid;place-items:center;background:
    radial-gradient(1200px 600px at 50% -10%,#1a2128,transparent),var(--bg);
    color:var(--text);font-family:"Segoe UI","Microsoft YaHei",system-ui,-apple-system,sans-serif;}
  form{width:min(360px,calc(100% - 40px));background:var(--panel);border:1px solid var(--line);
    border-radius:14px;padding:26px 24px 22px;text-align:center;}
  .logo{width:46px;height:46px;margin:0 auto 12px;border-radius:10px;display:grid;place-items:center;
    background:linear-gradient(135deg,#3a2a12,#1c1b18);border:1px solid #4a3a1c;color:var(--gold);
    font-weight:800;font-size:17px;letter-spacing:.5px;}
  h1{font-size:17px;margin:0 0 6px;letter-spacing:.5px;}
  .sub{font-size:12px;color:var(--muted);line-height:1.6;margin:0 0 18px;}
  input{width:100%;padding:11px 13px;border-radius:9px;border:1px solid var(--line);
    background:#0c1014;color:var(--text);font-size:15px;outline:none;font-family:inherit;}
  input:focus{border-color:#6b5423;}
  .err{color:#ff7875;font-size:12px;min-height:16px;margin:8px 0 2px;}
  button{width:100%;margin-top:6px;padding:11px;border-radius:9px;cursor:pointer;font-size:15px;
    border:1px solid #6b5423;background:linear-gradient(180deg,#3b2f18,#2a2417);color:var(--gold);
    font-family:inherit;letter-spacing:.08em;}
  button:hover{background:linear-gradient(180deg,#48391c,#332c1b);}
</style></head>
<body>
<form method="post" action="/login">
  <div class="logo">DF</div>
  <h1>子弹行情终端</h1>
  <p class="sub">这是私人看板<br>输入访问口令后继续浏览</p>
  <input name="token" type="password" autocomplete="off" placeholder="访问口令" autofocus />
  <div class="err">{{MSG}}</div>
  <button type="submit">进 入</button>
</form>
</body></html>
"""


class Handler(BaseHTTPRequestHandler):
    store: Store
    monitor: Monitor
    server_version = "AmmoMonitor/1.0"
    share_token = ""        # 空 = 不校验
    readonly = False        # True = 拦所有写接口

    # --- 工具 ---
    def _json(self, obj, code: int = 200) -> None:
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _text(self, text: str, code: int = 200, ctype: str = "text/plain; charset=utf-8") -> None:
        body = text.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _read_json(self) -> dict:
        length = int(self.headers.get("Content-Length") or 0)
        if not length:
            return {}
        try:
            return json.loads(self.rfile.read(length).decode("utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError):
            return {}

    def log_message(self, fmt, *args):   # 静默访问日志，避免刷屏
        log.debug("HTTP %s", fmt % args)

    # --- 访问控制 ---
    def _cookie_token(self) -> str:
        raw = self.headers.get("Cookie") or ""
        for part in raw.split(";"):
            if "=" not in part:
                continue
            k, v = part.split("=", 1)
            if k.strip() == "ammo_token":
                return v.strip()
        return ""

    def _auth_ok(self) -> bool:
        if not self.share_token:
            return True
        return hmac.compare_digest(self._cookie_token(), self.share_token)

    def _serve_login(self, bad: bool = False) -> None:
        body = LOGIN_HTML.replace("{{MSG}}", "口令不对，请重试" if bad else "").encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _handle_login(self) -> None:
        length = int(self.headers.get("Content-Length") or 0)
        body = self.rfile.read(length).decode("utf-8", "ignore") if length else ""
        token = (parse_qs(body).get("token") or [""])[0].strip()
        if self.share_token and hmac.compare_digest(token, self.share_token):
            self.send_response(303)
            self.send_header(
                "Set-Cookie",
                f"ammo_token={quote(token, safe='')}; Path=/; Max-Age=604800; HttpOnly; SameSite=Lax",
            )
            self.send_header("Location", "/")
            self.send_header("Content-Length", "0")
            self.end_headers()
        else:
            self._serve_login(True)

    # --- 路由 ---
    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path
        qs = parse_qs(parsed.query)

        if path == "/healthz":
            self._json({"ok": True})
            return
        if path == "/login":
            self._serve_login()
            return
        if not self._auth_ok():
            if path.startswith("/api/"):
                self._json({"ok": False, "error": "需要访问口令", "need_token": True}, 401)
            else:
                self._serve_login()
            return

        try:
            if path in ("/", "/index.html"):
                self._serve_web("index.html")
            elif path.startswith("/web/"):
                self._serve_web(path[len("/web/"):])
            elif path == "/api/dashboard":
                self._api_dashboard()
            elif path == "/api/index":
                self._json({"ok": True, "index": self.store.index_state()})
            elif path == "/api/history":
                oid = (qs.get("oid") or [""])[0]
                limit = int((qs.get("limit") or ["200"])[0])
                self._json({"ok": True, "history": self.store.history(oid, min(limit, 600))})
            elif path == "/api/export.csv":
                self._api_export()
            elif path == "/api/sim/equity":
                limit = int((qs.get("limit") or ["200"])[0])
                self._json({"ok": True, "equity": self.store.sim_state(trade_limit=0)["equity"][-min(limit, 500):]})
            else:
                self._json({"ok": False, "error": "not found"}, 404)
        except Exception as e:      # 任何异常都别把服务打挂
            log.exception("GET %s 处理失败", path)
            self._json({"ok": False, "error": str(e)}, 500)

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path

        if path == "/login":
            self._handle_login()
            return

        payload = self._read_json()
        if not self._auth_ok():
            self._json({"ok": False, "error": "需要访问口令", "need_token": True}, 401)
            return
        if self.readonly:
            self._json({"ok": False, "error": "只读模式：访客不能修改数据"}, 403)
            return
        try:
            if path == "/api/watch":
                self.store.watch_upsert(payload)
                self.monitor.wake.set()
                self._json({"ok": True})
            elif path == "/api/watch/remove":
                self.store.watch_remove(str(payload.get("oid", "")))
                self._json({"ok": True})
            elif path == "/api/settings":
                changed = {}
                for k, v in (payload or {}).items():
                    if k in DEFAULT_SETTINGS:
                        default = DEFAULT_SETTINGS[k]
                        if isinstance(default, bool):
                            v = bool(v)
                        elif isinstance(default, int):
                            v = int(float(v))
                        elif isinstance(default, float):
                            v = float(v)
                        self.store.set_setting(k, v)
                        changed[k] = v
                if "share_token" in changed:       # 口令即时生效，不用重启
                    Handler.share_token = str(changed["share_token"] or "")
                if "readonly" in changed:
                    Handler.readonly = bool(changed["readonly"])
                self.monitor.wake.set()
                self._json({"ok": True, "changed": changed})
            elif path == "/api/refresh":
                self.monitor.wake.set()
                threading.Thread(
                    target=self.monitor.scan, args=("full",), kwargs={}, daemon=True
                ).start()
                self._json({"ok": True, "message": "已触发全量刷新"})
            elif path == "/api/alerts/clear":
                with self.store.lock, self.store.conn:
                    self.store.conn.execute("DELETE FROM alerts")
                self._json({"ok": True})
            elif path == "/api/sim/buy":
                self._json({"ok": True, "sim": self.store.sim_buy(payload.get("oid"), payload.get("qty"))})
            elif path == "/api/sim/sell":
                self._json({"ok": True, "sim": self.store.sim_sell(payload.get("oid"), payload.get("qty"))})
            elif path == "/api/sim/reset":
                self._json({"ok": True, "sim": self.store.sim_reset(payload.get("initial_cash"))})
            else:
                self._json({"ok": False, "error": "not found"}, 404)
        except Exception as e:
            log.exception("POST %s 处理失败", path)
            self._json({"ok": False, "error": str(e)}, 500)

    # --- 具体接口 ---
    def _serve_web(self, name: str) -> None:
        safe = os.path.normpath(os.path.join(WEB_DIR, name))
        if not safe.startswith(os.path.normpath(WEB_DIR)) or not os.path.isfile(safe):
            self._json({"ok": False, "error": "文件不存在"}, 404)
            return
        ctype = {
            ".html": "text/html; charset=utf-8",
            ".css": "text/css; charset=utf-8",
            ".js": "application/javascript; charset=utf-8",
            ".svg": "image/svg+xml",
            ".png": "image/png",
        }.get(os.path.splitext(safe)[1].lower(), "application/octet-stream")
        with open(safe, "rb") as f:
            body = f.read()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
        self.end_headers()
        self.wfile.write(body)

    def _api_dashboard(self) -> None:
        settings = self.store.all_settings()
        settings["readonly"] = bool(self.readonly)      # 以实际生效的开关为准（可能是命令行覆盖）
        items = self.store.items_overview(spark_points=40)
        alerts = self.store.recent_alerts(30)
        last_run = self.store.last_run()
        watch_count = len([w for w in self.store.watch_list() if w["enabled"]])
        self._json(
            {
                "ok": True,
                "state": self.monitor.status(),
                "settings": settings,
                "source": self.monitor.source.name,
                "items": items,
                "alerts": alerts,
                "last_run": last_run,
                "watch_count": watch_count,
                "sim": self.store.sim_state(),
            }
        )

    def _api_export(self) -> None:
        import csv
        import io

        buf = io.StringIO()
        writer = csv.writer(buf)
        writer.writerow(
            ["物品ID", "名称", "口径", "穿透等级", "品质档", "当前价", "较今日低点%", "距今日高点%",
             "今日最高", "今日最低", "关注", "买入价", "持仓数量", "最后更新"]
        )
        with self.store.lock:
            items = self.store.conn.execute("SELECT * FROM items ORDER BY name").fetchall()
            watch = {r["oid"]: dict(r) for r in self.store.conn.execute("SELECT * FROM watch").fetchall()}
        for it in items:
            w = watch.get(it["oid"], {})
            price, high, low = it["last_price"], it["high"], it["low"]
            high_gap = round((price - high) / high * 100, 2) if price and high else ""
            writer.writerow(
                [
                    it["oid"], it["name"], it["caliber"] or "",
                    pen_of(it["name"], it["grade"]), it["grade"] or 0,
                    price if price is not None else "",
                    it["day_pct"] if it["day_pct"] is not None else "",
                    high_gap,
                    high or "", low or "",
                    "是" if w else "否",
                    w.get("buy_price") or "", w.get("qty") or "",
                    datetime.fromtimestamp(it["last_seen"]).strftime("%Y-%m-%d %H:%M:%S") if it["last_seen"] else "",
                ]
            )
        fname = f"delta_ammo_{datetime.now():%Y%m%d_%H%M}.csv"
        self.send_response(200)
        body = buf.getvalue().encode("utf-8-sig")     # BOM 让 Excel 正确识别中文
        self.send_header("Content-Type", "text/csv; charset=utf-8")
        self.send_header("Content-Disposition", f'attachment; filename="{fname}"')
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


# --------------------------------------------------------------------------
# 启动
# --------------------------------------------------------------------------
def ensure_config() -> None:
    """首次运行写出一份可读的 config.json，方便手改。"""
    if os.path.exists(CONFIG_PATH):
        return
    cfg = {
        "_说明": "改完重启程序生效；带注释的默认值见 DEFAULT_SETTINGS。UI 里也能改大部分项。",
        **DEFAULT_SETTINGS,
    }
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)


def apply_config_file(store: Store) -> None:
    if not os.path.exists(CONFIG_PATH):
        return
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            cfg = json.load(f)
        for k, v in cfg.items():
            if k.startswith("_"):
                continue
            if k in DEFAULT_SETTINGS:
                store.set_setting(k, v)
    except (json.JSONDecodeError, OSError) as e:
        log.warning("config.json 读取失败，忽略：%s", e)


def port_in_use(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.settimeout(0.4)
        return s.connect_ex(("127.0.0.1", port)) == 0


def pick_port(preferred: int) -> int:
    if not port_in_use(preferred):
        return preferred
    for p in range(preferred + 1, preferred + 30):
        if not port_in_use(p):
            return p
    return preferred


def lan_ip() -> str:
    """取本机在局域网/出口网卡上的 IP，用于打印可分享地址。"""
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.connect(("223.5.5.5", 80))
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


def main() -> int:
    ap = argparse.ArgumentParser(description="三角洲行动 交易行子弹价格实时监控")
    ap.add_argument("--no-open", action="store_true", help="不自动打开浏览器")
    ap.add_argument("--once", action="store_true", help="只扫一次就退出")
    ap.add_argument("--verbose", action="store_true", help="输出调试日志")
    ap.add_argument("--host", default=None,
                    help="监听地址：默认读 config.json 的 host；对外共享用 0.0.0.0")
    ap.add_argument("--token", default=None, help="本次临时指定访问口令（覆盖 config.json）")
    ap.add_argument("--readonly", action="store_true", help="以只读模式启动（覆盖 config.json）")
    args = ap.parse_args()

    setup_logging(args.verbose)
    ensure_config()
    store = Store()
    apply_config_file(store)
    monitor = Monitor(store)

    if args.once:
        res = monitor.scan("full")
        print(json.dumps(res, ensure_ascii=False, indent=2))
        return 0 if res.get("ok") else 1

    settings = store.all_settings()
    port = pick_port(int(settings.get("port") or 8777))
    if port != int(settings.get("port") or 8777):
        log.warning("端口 %s 被占用，改用 %s", settings.get("port"), port)

    host = str(args.host or settings.get("host") or "127.0.0.1")
    token = (args.token if args.token is not None else str(settings.get("share_token") or "")).strip()

    Handler.store = store
    Handler.monitor = monitor
    Handler.share_token = token
    Handler.readonly = bool(settings.get("readonly") or False) or args.readonly
    server = ThreadingHTTPServer((host, port), Handler)
    server.daemon_threads = True

    monitor.start()

    local_url = f"http://127.0.0.1:{port}/"
    log.info("监控服务已启动：%s（监听 %s:%s）", local_url, host, port)
    if host not in ("127.0.0.1", "localhost", ""):
        log.info("局域网/公网可试：http://%s:%s/", lan_ip(), port)
    if token:
        log.info("已启用访问口令；浏览器首次打开会要求输入")
    if Handler.readonly:
        log.info("只读模式已开启：访客不能下单或改设置")
    log.info("数据库：%s", DB_PATH)
    log.info("关闭窗口或按 Ctrl+C 停止")

    if not args.no_open:
        threading.Timer(1.2, lambda: webbrowser.open(local_url)).start()

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        log.info("收到 Ctrl+C，正在退出")
    finally:
        monitor.stop()
        server.shutdown()
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
