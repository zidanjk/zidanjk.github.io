#!/usr/bin/env python3
"""一次性把本地 SQLite 的历史价格，转成静态版用的 history.json。

本地程序跑过的这几天已经积累了真实价格点，先把它灌进 history.json，
静态版上线第一刻就有曲线，而不是从空白开始。
"""
import json
import os
import sqlite3
import sys
import time
from datetime import datetime, timedelta, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import ammo_monitor as am  # noqa: E402

BJ = timezone(timedelta(hours=8))
BUCKET = 900
HIST_POINTS = 40
KEEP_DAYS = 400


def day0_of(ts: int) -> int:
    lt = datetime.fromtimestamp(ts, BJ)
    return int(datetime(lt.year, lt.month, lt.day, tzinfo=BJ).timestamp())


def main() -> int:
    db = os.path.join(ROOT, "data", "monitor.db")
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "docs", "ammo", "data", "history.json")
    if not os.path.exists(db):
        raise SystemExit("找不到 data/monitor.db")

    conn = sqlite3.connect(db)
    conn.row_factory = sqlite3.Row
    items = [dict(r) for r in conn.execute(
        "SELECT oid,name,grade,caliber,last_price FROM items"
    ).fetchall()]
    rows = conn.execute(
        "SELECT oid, ts, price FROM prices WHERE price IS NOT NULL ORDER BY ts"
    ).fetchall()
    first = {r["oid"]: r["price"] for r in conn.execute(
        "SELECT p.oid AS oid, p.price AS price FROM prices p "
        "JOIN (SELECT oid, MIN(ts) AS mt FROM prices GROUP BY oid) m "
        "ON m.oid = p.oid AND m.mt = p.ts"
    ).fetchall()}

    for it in items:
        it["pen"] = am.pen_of(it["name"], it["grade"])
    groups = {}
    for it in items:
        groups.setdefault(f"P{it['pen']}", []).append(it)
    order = [f"P{g}" for g in sorted(am.PEN_LABEL) if f"P{g}" in groups]
    keys = ["market"] + order

    hist_items = {}
    per_oid = {}
    for r in rows:
        per_oid.setdefault(r["oid"], []).append((int(r["ts"]), int(r["price"])))
    for it in items:
        oid = it["oid"]
        pts = per_oid.get(oid) or []
        bucket = {}
        for ts, price in pts:
            bucket[(ts // BUCKET) * BUCKET] = price
        h = [[ts, bucket[ts]] for ts in sorted(bucket)][-HIST_POINTS:]
        hist_items[oid] = {
            "n": it["name"], "g": it["grade"], "c": it["caliber"] or "", "pic": "",
            "base": first.get(oid) or it["last_price"],
            "base_ts": (per_oid.get(oid) or [(int(time.time()), 0)])[0][0],
            "hist": h,
        }

    # 按 15 分钟桶重算指数，口径与线上一致
    ts_map = {}
    for r in rows:
        ts_map.setdefault(int(r["ts"]), {})[r["oid"]] = int(r["price"])
    min_cover = max(3, int(len(items) * 0.6))
    running = {}
    pts_by_key = {k: [] for k in keys}
    daily = {}
    for ts in sorted(ts_map):
        running.update(ts_map[ts])
        if len(running) < min_cover:
            continue
        bk = (ts // BUCKET) * BUCKET
        d0 = day0_of(ts)
        for key in keys:
            members = items if key == "market" else groups[key]
            chgs = []
            for it in members:
                b = hist_items[it["oid"]]["base"]
                p = running.get(it["oid"])
                if not b or not p:
                    continue
                chgs.append((p / b - 1.0) * 100.0)
            if not chgs:
                continue
            v = round(am.INDEX_BASE * (1.0 + sum(chgs) / len(chgs) / 100.0), 2)
            line = pts_by_key[key]
            if line and line[-1][0] == bk:
                line[-1][1] = v
            else:
                line.append([bk, v])
            dl = daily.setdefault(key, [])
            if dl and dl[-1][0] == d0:
                row = dl[-1]
                row[2] = max(row[2], v); row[3] = min(row[3], v); row[4] = v
            else:
                dl.append([d0, v, v, v, v])
            if len(dl) > KEEP_DAYS:
                del dl[:-KEEP_DAYS]

    last_day = datetime.fromtimestamp((max(ts_map) if ts_map else int(time.time())), BJ).strftime("%Y-%m-%d")
    intraday = {"date": last_day, "ts": pts_by_key}

    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        json.dump({"v": 1, "updated": int(time.time()), "items": hist_items,
                   "intraday": intraday, "daily": daily}, f, ensure_ascii=False, separators=(",", ":"))
    print(f"已写入 {out}：{len(hist_items)} 种子弹 / 分时点 {len(pts_by_key['market'])} 个 / 日线 {len(daily.get('market') or [])} 根")
    return 0


if __name__ == "__main__":
    sys.exit(main())
