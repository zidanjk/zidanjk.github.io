#!/usr/bin/env python3
"""把抓取结果生成静态 JSON，供 GitHub Pages 版看板读取。

GitHub Actions 每次运行：
  1. 读取上一次提交的 history.json（累加历史）
  2. 抓一次交易行全量数据
  3. 算出大盘 / 各板块指数、分时、日/周/月/年 K、领涨领跌
  4. 写出 dashboard.json / index.json / history.json

之所以自己维护 JSON 而不是复用 SQLite：Actions 是无状态环境，
每轮都要把完整历史带回来，JSON 比数据库小得多，也方便 Pages 直接用。
"""
import argparse
import json
import os
import sys
import time
from datetime import datetime, timedelta, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import ammo_monitor as am  # noqa: E402  复用数据源适配器与口径函数

BJ = timezone(timedelta(hours=8))
BUCKET = 900          # 15 分钟一个分时点，与本地版一致
KEEP_DAYS = 400       # 日线保留天数
HIST_POINTS = 40      # 每个子弹保留最近多少个价格点


def bj_now() -> datetime:
    return datetime.now(BJ)


def day0_of(ts: int) -> int:
    lt = datetime.fromtimestamp(ts, BJ)
    return int(datetime(lt.year, lt.month, lt.day, tzinfo=BJ).timestamp())


def day_key(ts: int) -> str:
    return datetime.fromtimestamp(ts, BJ).strftime("%Y-%m-%d")


def load_json(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_json(path: str, obj) -> int:
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, path)
    return os.path.getsize(path)


def period_start(ts: int, period: str) -> int:
    lt = datetime.fromtimestamp(ts, BJ)
    if period == "day":
        base = datetime(lt.year, lt.month, lt.day, tzinfo=BJ)
    elif period == "week":
        base = datetime(lt.year, lt.month, lt.day, tzinfo=BJ) - timedelta(days=lt.weekday())
    elif period == "month":
        base = datetime(lt.year, lt.month, 1, tzinfo=BJ)
    else:
        base = datetime(lt.year, 1, 1, tzinfo=BJ)
    return int(base.timestamp())


def candles_from_daily(daily: list, period: str) -> list:
    """把日线聚合成周/月/年 K。daily 每行 [day0, o, h, l, c]。"""
    out: dict[int, list] = {}
    for row in daily:
        d0, o, h, l, c = row[0], row[1], row[2], row[3], row[4]
        ps = period_start(d0, period)
        cur = out.get(ps)
        if cur is None:
            out[ps] = [ps, o, h, l, c]
        else:
            cur[1] = o                     # 区间第一根的开盘价
            cur[2] = max(cur[2], h)
            cur[3] = min(cur[3], l)
            cur[4] = c
    return [row for _, row in sorted(out.items())]


def save_csv(path: str, items: list, now: int) -> int:
    import csv
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["名称", "口径", "穿透等级", "当前价(每发)", "较今日低点%", "今日高", "今日低", "快照时间"])
        sn = datetime.fromtimestamp(now, BJ).strftime("%Y-%m-%d %H:%M")
        for it in items:
            w.writerow([it["name"], it["caliber"], it["pen"], it["last_price"],
                        "" if it.get("day_pct") is None else round(it["day_pct"], 2),
                        it.get("high"), it.get("low"), sn])
    os.replace(tmp, path)
    return os.path.getsize(path)


def build(outdir: str, verbose: bool = True) -> dict:
    now = int(time.time())
    hist_path = os.path.join(outdir, "history.json")
    hist = load_json(hist_path)
    items_hist: dict = hist.get("items") or {}
    intraday: dict = hist.get("intraday") or {}
    daily: dict = hist.get("daily") or {}

    src = am.SixOwSource(gap_ms=200)
    rows, pages = src.fetch_all()
    rows = [r for r in rows if r.get("price")]
    if len(rows) < 20:
        raise SystemExit(f"只拿到 {len(rows)} 条子弹数据，可能被限流，本轮不写文件")

    # ---- 更新每种子弹的基期与价格历史 ----
    bk = (now // BUCKET) * BUCKET
    for r in rows:
        oid = r["oid"]
        st = items_hist.get(oid)
        if st is None:
            st = items_hist[oid] = {"base": r["price"], "base_ts": now, "hist": []}
        st["n"] = r["name"]
        st["g"] = r["grade"]
        st["c"] = r["caliber"] or ""
        st["pic"] = r["pic"] or ""
        if not st.get("base"):
            st["base"] = r["price"]
            st["base_ts"] = now
        h = st.setdefault("hist", [])
        if h and h[-1][0] >= bk:
            h[-1] = [bk, r["price"]]
        else:
            h.append([bk, r["price"]])
        del h[:-HIST_POINTS]
        r["pen"] = am.pen_of(r["name"], r["grade"])

    # ---- 分板块聚合 ----
    groups: dict = {}
    for r in rows:
        groups.setdefault(f"P{r['pen']}", []).append(r)
    order = [f"P{g}" for g in sorted(am.PEN_LABEL) if f"P{g}" in groups]
    label = {f"P{g}": v for g, v in am.PEN_LABEL.items()}
    keys = ["market"] + order
    members_of = {k: (rows if k == "market" else groups[k]) for k in keys}
    bases = {oid: st["base"] for oid, st in items_hist.items()}

    def agg(members: list) -> dict:
        chgs, up, down = [], 0, 0
        for r in members:
            b, p = bases.get(r["oid"]), r["price"]
            if not b or not p:
                continue
            chg = (p / b - 1.0) * 100.0
            chgs.append(chg)
            if chg > 0.01:
                up += 1
            elif chg < -0.01:
                down += 1
        avg = sum(chgs) / len(chgs) if chgs else 0.0
        return {
            "value": round(am.INDEX_BASE * (1.0 + avg / 100.0), 2),
            "chg": round(avg, 2),
            "cnt": len(chgs),
            "up": up,
            "down": down,
            "flat": len(chgs) - up - down,
        }

    # 覆盖不足六成的板块不出点，避免早期假跳
    min_cover = max(3, int(len(rows) * 0.6))
    today_k = day_key(now)
    if intraday.get("date") != today_k:
        intraday = {"date": today_k, "ts": {}}
    pts: dict = intraday.setdefault("ts", {})

    market = agg(rows)
    sectors = []
    values: dict = {}
    for key in keys:
        m = agg(members_of[key])
        values[key] = m["value"]
        if m["cnt"] >= min_cover:
            line = pts.setdefault(key, [])
            if line and line[-1][0] == bk:
                line[-1][1] = m["value"]
            else:
                line.append([bk, m["value"]])
        if key != "market":
            m.update({"key": key, "name": label.get(key, key)})
            sectors.append(m)
    market.update({"key": "market", "name": "大盘"})

    # ---- 日线更新 ----
    d0 = day0_of(now)
    for key in keys:
        line = daily.setdefault(key, [])
        v = values[key]
        if line and line[-1][0] == d0:
            row = line[-1]
            row[2] = max(row[2], v)
            row[3] = min(row[3], v)
            row[4] = v
        else:
            line.append([d0, v, v, v, v])
        if len(line) > KEEP_DAYS:
            del line[:-KEEP_DAYS]

    # ---- 领涨 / 领跌 ----
    ranked = []
    for r in rows:
        b = bases.get(r["oid"])
        if not b:
            continue
        ranked.append({
            "oid": r["oid"], "name": r["name"], "grade": r["grade"], "pen": r["pen"],
            "price": r["price"], "chg": round((r["price"] / b - 1.0) * 100.0, 2),
        })
    ranked.sort(key=lambda x: x["chg"], reverse=True)

    def rank_block(key: str, top: int = 6) -> dict:
        sub = ranked if key == "market" else [x for x in ranked if x["pen"] == int(key[1:])]
        return {"leaders": sub[:top], "laggers": list(reversed(sub[-top:])) if sub else [], "cnt": len(sub)}

    ranks = {k: rank_block(k) for k in keys}

    # ---- 组装 index.json ----
    def downsample(seq: list, n: int = 60) -> list:
        if len(seq) <= n:
            return seq
        step = len(seq) / float(n)
        out = [seq[min(len(seq) - 1, int(i * step))] for i in range(n)]
        out[-1] = seq[-1]
        return out

    series = {k: downsample(pts.get(k) or []) for k in keys}
    today = {k: downsample(pts.get(k) or []) for k in keys}
    kline = {"day": {k: candles_from_daily(daily.get(k) or [], "day") for k in keys}}
    for p in ("week", "month", "year"):
        kline[p] = {k: candles_from_daily(daily.get(k) or [], p) for k in keys}
    candles = {k: downsample(pts.get(k) or []) for k in keys}

    index_payload = {
        "ts": now,
        "count": len(rows),
        "base_note": "基期=每种子弹首个记录价",
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
        "static": True,
    }

    # ---- 组装 dashboard.json ----
    items_out = []
    for r in rows:
        st = items_hist[r["oid"]]
        h = st.get("hist") or []
        items_out.append({
            "oid": r["oid"],
            "name": r["name"],
            "caliber": r["caliber"] or "",
            "grade": r["grade"],
            "pen": r["pen"],
            "last_price": r["price"],
            "day_pct": r.get("day_pct"),
            "high": r.get("high"),
            "low": r.get("low"),
            "pic": st.get("pic") or "",
            "spark": [p for _, p in h][-30:],
            "hist": h,
            "watch": False,
            "w": None,
            "last_seen": now,
        })
    items_out.sort(key=lambda x: (x["last_price"] or 0), reverse=True)

    dash = {
        "ok": True,
        "static": True,
        "state": {
            "running": False,
            "ok": True,
            "mode": "static",
            "last_scan_ts": now,
            "next_scan_ts": 0,
            "full_items": len(rows),
            "full_pages": pages,
        },
        "settings": {
            "readonly": True, "sound": False, "flash": True,
            "alert_jump_pct": 3.0, "alert_day_pct": 8.0,
            "fee_rate": 5.0, "sim_buy_fee_pct": 0.0, "sim_sell_fee_pct": 15.0,
        },
        "source": src.name,
        "items": items_out,
        "alerts": [],
        "last_run": {"ts": now, "mode": "static", "items": len(rows), "ok": 1},
        "watch_count": 0,
        "sim": {"cash": 0, "positions": [], "trades": [], "equity": [],
                "initial_cash": 0, "market_value": 0, "total": 0, "roi": 0, "realized": 0, "floating": 0},
    }

    hist_out = {"v": 1, "updated": now, "items": items_hist, "intraday": intraday, "daily": daily}
    sizes = {
        "history.json": save_json(hist_path, hist_out),
        "dashboard.json": save_json(os.path.join(outdir, "dashboard.json"), dash),
        "index.json": save_json(os.path.join(outdir, "index.json"), {"ok": True, "index": index_payload}),
        "items.csv": save_csv(os.path.join(outdir, "items.csv"), items_out, now),
    }
    if verbose:
        print(f"子弹 {len(rows)} 种 / 板块 {len(order)} 个 / 分时点 {len(pts.get('market') or [])} 个")
        print("写出：" + "，".join(f"{k}={v/1024:.1f}KB" for k, v in sizes.items()))
    return {"items": len(rows), "sizes": sizes}


def main() -> int:
    ap = argparse.ArgumentParser(description="生成 GitHub Pages 静态数据")
    ap.add_argument("--out", default=os.path.join(ROOT, "ammo", "data"),
                    help="输出目录（默认 ammo/data）")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    res = build(args.out, verbose=not args.quiet)
    return 0 if res else 1


if __name__ == "__main__":
    sys.exit(main())

