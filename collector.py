#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
安全可靠测评结果采集器
======================
从中国信息安全测评中心「安全可靠测评」频道抓取全部《安全可靠测评结果公告》，
解析出产品条目，生成 data.json 与 index.html。

用法:
    python collector.py              # 抓取并生成
    python collector.py --offline    # 不联网，用已有 data.json 重新生成 index.html

退出码: 0 成功；1 抓取或解析失败（此时不会覆盖已有的 index.html）
"""

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import date, datetime, timezone

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_FILE = os.path.join(BASE_DIR, "data.json")
INDEX_FILE = os.path.join(BASE_DIR, "index.html")
TEMPLATE_FILE = os.path.join(BASE_DIR, "template.html")

LIST_URL = "https://www.itsec.gov.cn/aqkkcp/cpgg/"
SITE = "https://www.itsec.gov.cn/aqkkcp/cpgg/"
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36"

# ---------------------------------------------------------------- 网络

def fetch(url, tries=3, timeout=30):
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={
                "User-Agent": UA,
                "Accept-Language": "zh-CN,zh;q=0.9",
            })
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read().decode("utf-8", "replace")
        except Exception as e:                      # noqa: BLE001
            last = e
            if i + 1 < tries:
                time.sleep(1.5 * (i + 1))
    raise RuntimeError("抓取失败 %s: %s" % (url, last))


# ---------------------------------------------------------------- 解析

CATEGORY_KEYWORDS = [
    ("中央处理器", "cpu"),
    ("人工智能训练推理芯片", "ai"),
    ("打印机主控芯片", "printer"),
    ("操作系统", "os"),
    ("数据库", "db"),
]

SUBCATEGORY_KEYWORDS = [
    ("桌面操作系统", "os-desktop"),
    ("服务器操作系统", "os-server"),
    ("集中式数据库", "db-central"),
    ("分布式数据库", "db-dist"),
]

ROMAN = {"Ⅲ": 3, "Ⅱ": 2, "Ⅰ": 1, "III": 3, "II": 2, "I": 1}

WS = re.compile(r"\s+")
KERNEL_RE = re.compile(r"[（(]\s*内核版本\s*(.+?)\s*[）)]")


def clean(text):
    """折叠空白、去不换行空格。"""
    if text is None:
        return ""
    t = text.replace("\u00a0", " ").replace("\u3000", " ")
    return WS.sub(" ", t).strip()


def norm_level(cell):
    """把 'Ⅲ级' / 'II级' / 'Ⅰ级' 归一为 1/2/3，识别不了返回 None。"""
    t = clean(cell)
    for token, val in sorted(ROMAN.items(), key=lambda kv: -len(kv[0])):
        if token in t:
            return val
    m = re.search(r"([ⅠⅡⅢIVX]{1,3})\s*级", t)
    if m:
        return ROMAN.get(m.group(1))
    return None


def split_name_kernel(raw):
    """从产品名称单元格拆出名称与内核版本。"""
    name = clean(raw)
    kernel = ""
    m = KERNEL_RE.search(name)
    if m:
        kernel = clean(m.group(1))
        name = clean(name[: m.start()] + " " + name[m.end():])
    # 去掉名称尾部残留的全角/半角括号空壳
    name = re.sub(r"[（(]\s*[）)]", "", name).strip()
    return name, kernel


def category_of(title):
    for kw, key in CATEGORY_KEYWORDS:
        if kw in title:
            return key
    return None


def subcategory_of(title):
    for kw, key in SUBCATEGORY_KEYWORDS:
        if kw in title:
            return key
    return None


def subcategory_of_name(name):
    """附表未分（一）（二）小标题时，从产品名称里推断细分类型。"""
    if "桌面" in name:
        return "os-desktop"
    if "服务器" in name or "Server" in name:
        return "os-server"
    return None


def parse_announcement(page_html, url, period_label, period_key):
    """解析一期公告，返回 (meta, rows, unknown_titles)。"""
    from lxml import html as LH

    doc = LH.fromstring(page_html)
    body_text = clean(doc.text_content())

    # 优先取正文头部的日期节点，取不到再退化为全文首个日期
    date_node = doc.xpath("//*[contains(@class,'date')]/text()")
    m = None
    if date_node:
        m = re.search(r"(\d{4})-(\d{2})-(\d{2})", clean(" ".join(date_node)))
    if not m:
        m = re.search(r"(\d{4})-(\d{2})-(\d{2})", body_text)
    if not m:
        raise RuntimeError("找不到公告日期: %s" % url)
    ann_date = "%s-%s-%s" % (m.group(1), m.group(2), m.group(3))

    mg = re.search(r"根据《([^》]+)》要求", body_text)
    guide = mg.group(1) if mg else ""

    rows = []
    warnings = {"unknownTables": [], "skippedRows": []}
    tables = doc.xpath("//table")
    for tbl in tables:
        # 向前收集兄弟节点的文字，定位「附表X、…」与「（一）…」小标题
        prev_texts = []
        node = tbl.getprevious()
        hops = 0
        while node is not None and hops < 10:
            t = clean(node.text_content())
            if t:
                prev_texts.append(t)
            node = node.getprevious()
            hops += 1
        prev_texts.reverse()          # 变为文档顺序

        ann_title = ""
        ann_idx = -1
        for i, t in enumerate(prev_texts):
            if "附表" in t:
                ann_title, ann_idx = t, i
        if not ann_title:
            continue                  # 不是结果表（例如页脚表格）

        sub_title = ""
        for t in prev_texts[ann_idx + 1:]:
            if re.match(r"^[（(][一二三四五六七八九十]+[）)]", t):
                sub_title = t

        # 附表标题去掉括注后取类别
        title_core = re.sub(r"[（(][^）)]*[）)]", "", ann_title)
        title_core = re.sub(r"^附表[一二三四五六七八九十]+[、.]\s*", "", title_core)
        cat = category_of(title_core) or category_of(ann_title)
        sub = subcategory_of(sub_title) or subcategory_of(ann_title)
        if not cat:
            # 附表存在却认不出类别：说明官网新增了测评对象，需要人工补关键词
            warnings["unknownTables"].append(ann_title)
            continue

        for tr in tbl.xpath(".//tr"):
            cells = tr.xpath("./td|./th")
            if len(cells) < 4:
                continue
            texts = [clean(c.text_content()) for c in cells]
            if not re.fullmatch(r"\d+", texts[0] or ""):
                continue              # 表头或分隔行
            name, kernel = split_name_kernel(texts[1])
            vendor = texts[2]
            level = norm_level(texts[3])
            if not name or not vendor or level is None:
                # 有序号却解析不完整：属于静默丢数据，要显式报出来
                warnings["skippedRows"].append("%s 第 %s 行: %s" % (period_label, texts[0], " / ".join(texts)))
                continue
            item = {
                "n": name,
                "v": vendor,
                "c": cat,
                "lv": level,
                "a": period_key,
            }
            if kernel:
                item["k"] = kernel
            if sub:
                item["s"] = sub
            elif cat == "os":
                inferred = subcategory_of_name(name)
                if inferred:
                    item["s"] = inferred
            rows.append(item)

    meta = {
        "label": period_label,
        "date": ann_date,
        "guide": guide,
        "url": url,
    }
    return meta, rows, warnings


def parse_list(list_html):
    """从列表页提取公告链接，返回 [(period_key, period_label, url), ...]"""
    items = []
    seen = set()
    for m in re.finditer(
        r'href="\./(\d{6})/t(\d{8})_(\d+)\.html"[^>]*title="([^"]*)"', list_html
    ):
        folder, ymd, aid, title = m.groups()
        if aid in seen:
            continue
        seen.add(aid)
        lm = re.search(r"（(\d{4})年第(\d+)号）", title)
        if not lm:
            continue
        year, no = lm.group(1), int(lm.group(2))
        label = "%s年第%d号" % (year, no)
        items.append(("%s-%d" % (year, no), label, SITE + folder + "/t" + ymd + "_" + aid + ".html", title))
    return items


# ---------------------------------------------------------------- 主流程

def load_previous():
    """读取上一份 data.json，用于单期失败时回填，避免整期条目被抹掉。"""
    if not os.path.exists(DATA_FILE):
        return None
    try:
        with open(DATA_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:                               # noqa: BLE001
        return None


def carry_over(payload, previous):
    """本期抓取失败的公告期，沿用上次已采到的公告元信息与产品条目。"""
    if not previous:
        return 0
    failed_keys = set()
    for line in payload["failures"]:
        failed_keys.add(line.split(":", 1)[0].strip())
    if not failed_keys:
        return 0

    # failures 里是 label（如「2026年第3号」），转回 period key
    label_to_key = {v["label"]: k for k, v in previous.get("announcements", {}).items()}
    rescued_keys = {label_to_key[lb] for lb in failed_keys if lb in label_to_key}
    if not rescued_keys:
        return 0

    carried = 0
    for k in rescued_keys:
        meta = previous["announcements"][k]
        rows = [p for p in previous.get("products", []) if p.get("a") == k]
        if not rows:
            continue
        payload["announcements"][k] = meta
        payload["products"].extend(rows)
        carried += len(rows)
        print("      ↩ %s 抓取失败，沿用上次 %d 条记录" % (meta["label"], len(rows)))

    if carried:
        payload["carriedOver"] = sorted(
            "%s(%d 条)" % (previous["announcements"][k]["label"],
                           sum(1 for p in previous.get("products", []) if p.get("a") == k))
            for k in rescued_keys
        )
    return carried


def collect():
    print("[1/3] 拉取公告列表 …")
    list_html = fetch(LIST_URL)
    entries = parse_list(list_html)
    if not entries:
        raise RuntimeError("列表页未解析到任何公告，页面结构可能已变更")
    print("      发现 %d 期公告" % len(entries))

    previous = load_previous()

    print("[2/3] 逐期解析 …")
    ann = {}
    products = []
    failures = []
    unknown_tables = []
    skipped_rows = []
    for key, label, url, title in entries:
        try:
            page = fetch(url)
            meta, rows, warns = parse_announcement(page, url, label, key)
        except Exception as e:                      # noqa: BLE001
            failures.append("%s: %s" % (label, e))
            print("      ✗ %s 解析失败: %s" % (label, e))
            continue
        if not rows and previous and any(
            p.get("a") == key for p in previous.get("products", [])
        ):
            # 页面能打开却一条也解析不出，说明表格结构变了，不能当作「该期没产品」
            failures.append("%s: 解析结果为空，疑似页面结构变更" % label)
            print("      ✗ %s 解析结果为空（此前有数据），疑似页面结构变更" % label)
            continue
        ann[key] = meta
        products.extend(rows)
        unknown_tables.extend(warns["unknownTables"])
        skipped_rows.extend(warns["skippedRows"])
        print("      ✓ %s  %s  %d 条" % (meta["date"], label, len(rows)))
        for w in warns["skippedRows"]:
            print("        ! 跳过无法解析的行 %s" % w)

    if not products:
        raise RuntimeError("没有解析到任何产品条目；未覆盖旧文件")

    for t in unknown_tables:
        print("      ! 附表标题无法识别类别：%s" % t)

    payload = {
        "generatedAt": datetime.now(timezone.utc).astimezone().isoformat(timespec="seconds"),
        "source": LIST_URL,
        "announcements": ann,
        "products": products,
        "failures": failures,
        "unknownTables": unknown_tables,
        "skippedRows": skipped_rows,
    }
    carried = carry_over(payload, previous)

    # 稳定排序：期号升序
    def ann_order(k):
        y, n = k.split("-")
        return (int(y), int(n))

    payload["announcements"] = {
        k: payload["announcements"][k]
        for k in sorted(payload["announcements"], key=ann_order)
    }
    if carried:
        print("      ↩ 共沿用 %d 条历史记录（%d 期抓取失败）" % (carried, len(failures)))
    return payload


def write_outputs(payload, regenerate_only=False):
    with open(DATA_FILE, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=1)
    print("      已写入 %s" % os.path.basename(DATA_FILE))

    if not os.path.exists(TEMPLATE_FILE):
        print("      ! 缺少 template.html，跳过 index.html 生成")
        return
    with open(TEMPLATE_FILE, "r", encoding="utf-8") as f:
        tpl = f.read()

    ann_json = json.dumps(payload["announcements"], ensure_ascii=False, indent=1)
    data_json = json.dumps(payload["products"], ensure_ascii=False, indent=1)
    html = tpl.replace("__ANN__", ann_json).replace("__DATA__", data_json)
    html = html.replace("__GENERATED__", payload["generatedAt"])
    html = html.replace("__ANNCOUNT__", str(len(payload["announcements"])))
    html = html.replace("__YEARSPAN__", year_span(payload["announcements"]))

    with open(INDEX_FILE, "w", encoding="utf-8") as f:
        f.write(html)
    print("      已写入 %s" % os.path.basename(INDEX_FILE))


def year_span(ann):
    years = sorted({v["date"][:4] for v in ann.values()})
    if not years:
        return "—"
    if len(years) == 1:
        return years[0]
    return "%s—%s" % (years[0], years[-1])


def main():
    ap = argparse.ArgumentParser(description="安全可靠测评结果采集器")
    ap.add_argument("--offline", action="store_true", help="不联网，用已有 data.json 重新生成 index.html")
    args = ap.parse_args()

    if args.offline:
        if not os.path.exists(DATA_FILE):
            print("! data.json 不存在，无法离线生成", file=sys.stderr)
            return 1
        with open(DATA_FILE, "r", encoding="utf-8") as f:
            payload = json.load(f)
        print("[离线] 使用已有 data.json 重新生成 …")
        write_outputs(payload, regenerate_only=True)
        return 0

    try:
        payload = collect()
    except Exception as e:                          # noqa: BLE001
        print("! 采集失败: %s" % e, file=sys.stderr)
        print("! 已保留原有的 data.json / index.html 不变", file=sys.stderr)
        return 1

    print("[3/3] 生成文件 …")
    write_outputs(payload)
    print("完成：%d 期公告，%d 条产品记录" % (len(payload["announcements"]), len(payload["products"])))
    if payload["failures"]:
        print("注意：%d 期解析失败" % len(payload["failures"]))
    if payload.get("skippedRows"):
        print("注意：%d 行因字段不完整被跳过（见 data.json 的 skippedRows）" % len(payload["skippedRows"]))
    if payload.get("unknownTables"):
        print("注意：%d 个附表无法识别类别（见 data.json 的 unknownTables）" % len(payload["unknownTables"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
