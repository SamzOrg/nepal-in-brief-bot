"""Nepal In Brief: RSS -> dedupe -> translate (EN<->NE) -> branded images -> Facebook Page + Instagram.

Every story is posted twice (English + Nepali), never more. Run every 30 min (GitHub Actions).
One LLM request per run (Groq gpt-oss-120b, falling back to Gemini Flash-Lite), only for items
never seen before, only to translate headlines + flag duplicates. If both fail, those items
retry on the next run.

Env (GitHub Secrets): GROQ_API_KEY, GEMINI_API_KEY (backup), FB_PAGE_ID, FB_PAGE_TOKEN, IG_USER_ID
Optional env: DRY_RUN=1 (render + print only, no posting, state untouched)
"""
import calendar, html, json, os, re, pathlib, sys, time, traceback
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from urllib.parse import urlsplit, urlunsplit, parse_qsl, urlencode

import feedparser, requests
from PIL import Image, ImageDraw, ImageFont

# ================= CONFIG =================
BRAND          = "NEPAL IN BRIEF"
# Translation + duplicate flags. Groq first; Gemini only if Groq fails (limit, outage, key issue).
# Max 1 successful request per run.
GROQ_X = {"reasoning_effort": "low", "include_reasoning": False}
PROVIDERS = [
    ("groq gpt-oss-120b", "https://api.groq.com/openai/v1/chat/completions",
     "GROQ_API_KEY",   "openai/gpt-oss-120b",      GROQ_X),
    ("gemini flash-lite", "https://generativelanguage.googleapis.com/v1beta/openai/chat/completions",
     "GEMINI_API_KEY", "gemini-flash-lite-latest", {}),
]
GRAPH          = "https://graph.facebook.com/v23.0"
MAX_AGE_H      = 8      # stories older than this are dropped (seen + queue)
LLM_BATCH      = 25     # max new items per LLM request (Groq free TPM is 8K, so keep <= ~30)
STORIES_PER_RUN = 2     # each story = 1 EN + 1 NE post on each platform
FB_DAILY_CAP   = 200    # FB posts per rolling 24h (no hard API cap; lower it if reach drops)
IG_DAILY_CAP   = 96     # IG API hard limit is 100 per rolling 24h
DUP_JACCARD    = 0.5    # word-overlap threshold for local duplicate detection
HASHTAGS_EN    = "#Nepal #NepalNews #NepalInBrief"
HASHTAGS_NE    = "#नेपाल #समाचार #NepalInBrief"

NEPAL = re.compile(r"\b(nepal\w*|kathmandu|pokhara|lumbini|everest|sagarmatha|himalaya\w*|"
                   r"terai|madhesh|gurkha\w*|gorkha\w*|lalitpur|bhaktapur|biratnagar|birgunj|"
                   r"chitwan|janakpur)\b", re.I)

# (name, url, needs_nepal_filter, weight). Weight breaks ties when ranking the queue.
FEEDS = [
    # Nepal, Nepali language
    ("Onlinekhabar",    "https://www.onlinekhabar.com/feed",              False, 3),
    ("Nagarik News",    "https://nagariknews.nagariknetwork.com/feed",    False, 3),
    ("Setopati",        "https://www.setopati.com/feed",                  False, 3),
    ("Ratopati",        "https://www.ratopati.com/feed",                  False, 3),
    # Nepal, English
    ("Kathmandu Post",  "https://kathmandupost.com/rss",                  False, 3),
    ("Onlinekhabar EN", "https://english.onlinekhabar.com/feed",          False, 3),
    ("Himalayan Times", "https://thehimalayantimes.com/rssFeed/15",       False, 3),
    ("Rising Nepal",    "https://risingnepaldaily.com/rss",               False, 2),
    # International, only items that mention Nepal
    ("Google News",     "https://news.google.com/rss/search?q=Nepal+when:1d&hl=en-US&gl=US&ceid=US:en", True, 2),
    ("Google News IN",  "https://news.google.com/rss/search?q=Nepal+when:1d&hl=en-IN&gl=IN&ceid=IN:en", True, 2),
    ("Al Jazeera",      "https://www.aljazeera.com/xml/rss/all.xml",      True, 3),
    ("BBC Asia",        "https://feeds.bbci.co.uk/news/world/asia/rss.xml", True, 3),
    ("The Guardian",    "https://www.theguardian.com/world/nepal/rss",    True, 3),
]

# ---- image ----
HERE      = pathlib.Path(__file__).parent
TEMPLATE  = HERE / "assets" / "template.jpg"   # branded template (1254x1254); headline goes in the panel
BOX       = (100, 490, 1054, 420)              # headline area inside the panel: left, top, width, height
TEXT_RGB  = (255, 255, 255)
FONT_BOLD = [HERE / "assets" / "fonts" / "headline.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"]
# ==========================================

STATE = HERE / "state.json"
OUT   = HERE / "out"
NPT   = timezone(timedelta(hours=5, minutes=45))
DRY   = os.getenv("DRY_RUN") == "1"
UA    = {"User-Agent": "Mozilla/5.0 (NepalInBrief bot)"}
DEVA  = re.compile(r"[ऀ-ॿ]")

REPL = {"‘": "'", "’": "'", "“": '"', "”": '"',
        "–": "-", "—": "-", "…": "...", " ": " "}


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def clean(s):
    s = html.unescape(re.sub(r"<[^>]+>", " ", s or ""))
    for k, v in REPL.items():
        s = s.replace(k, v)
    s = re.sub(r"The post .{0,200}? appeared first on .*$", "", s)  # WordPress footer
    return re.sub(r"\s+", " ", s).strip()


def norm_link(u):
    p = urlsplit((u or "").strip())
    q = [(k, v) for k, v in parse_qsl(p.query) if not k.lower().startswith(("utm_", "fbclid"))]
    return urlunsplit((p.scheme, p.netloc, p.path, urlencode(q), ""))


def words(s):
    return {w for w in re.findall(r"[\wऀ-ॿ]+", s.lower()) if len(w) > 2}


def similar(a, b):
    a, b = words(a), words(b)
    return bool(a and b) and len(a & b) / len(a | b) >= DUP_JACCARD


def shorten(s, n):
    return s if len(s) <= n else s[:n].rsplit(" ", 1)[0] + "..."


# ---------------- fetch ----------------
def fetch(feed):
    name, url, needs_nepal, weight = feed
    try:
        r = requests.get(url, timeout=20, headers=UA)
        r.raise_for_status()
        entries = feedparser.parse(r.content).entries
    except Exception as ex:
        log(f"FEED FAIL {name}: {ex!r}")
        return []
    now, out = time.time(), []
    for e in entries:
        pub = e.get("published_parsed") or e.get("updated_parsed")
        ts = calendar.timegm(pub) if pub else now
        if now - ts > MAX_AGE_H * 3600:
            continue
        title, summary, src = clean(e.get("title")), clean(e.get("summary")), name
        if name.startswith("Google News"):  # "Headline - Publisher", summary is just link soup
            src = (e.get("source") or {}).get("title") or name
            title, summary = re.sub(rf"\s+-\s+{re.escape(src)}$", "", title), ""
        if needs_nepal and not NEPAL.search(f"{title} {summary}"):
            continue
        link = norm_link(e.get("link"))
        if title and link:
            out.append({"title": title, "summary": shorten(summary, 220), "link": link,
                        "source": src, "ts": ts, "weight": weight,
                        "lang": "ne" if DEVA.search(title) else "en"})
    log(f"{name}: {len(out)} fresh")
    return out


# ---------------- translation (1 LLM request per run) ----------------
PROMPT = """Translate news headlines for a Nepal news page and flag duplicates.

For each NEW item:
- "t": the headline translated into the OTHER language ([ne] item -> English, [en] item -> Nepali in
  Devanagari). Faithful, concise, news-headline style, max 100 characters, no added facts, no quotes.
- "d": if it reports the SAME event as an EXISTING story or an EARLIER new item, give that ref
  ("E3" or "5"); otherwise null.

Respond with JSON only: {{"r": [{{"i": 0, "t": "...", "d": null}}]}} with one entry per new item.

EXISTING:
{existing}

NEW:
{new}
"""


def llm_translate(batch, existing):
    prompt = PROMPT.format(
        existing="\n".join(f"E{i}: {t}" for i, t in enumerate(existing)) or "(none)",
        new="\n".join(f"{i} [{b['lang']}] {b['title']}" for i, b in enumerate(batch)))
    for name, url, key_env, model, extra in PROVIDERS:
        key = os.getenv(key_env)
        if not key:
            continue
        try:
            r = requests.post(url, headers={"Authorization": f"Bearer {key}"}, timeout=90,
                              json={"model": model, "temperature": 0.1, "max_completion_tokens": 6000,
                                    "response_format": {"type": "json_object"},
                                    "messages": [{"role": "user", "content": prompt}], **extra})
            if r.status_code != 200:
                raise RuntimeError(f"{r.status_code}: {r.text[:200]}")
            text = r.json()["choices"][0]["message"]["content"]
            text = text[text.find("{"):text.rfind("}") + 1]  # tolerate ```json fences
            rows = json.loads(text)["r"]
            log(f"LLM ok via {name}")
            return {int(x["i"]): (clean(x.get("t", "")), x.get("d")) for x in rows if "i" in x}
        except Exception as ex:
            log(f"LLM {name} failed: {ex!r}")
    raise RuntimeError("all LLM providers failed")


def translate(batch, existing):
    """Raises if both models fail; caller then leaves the items unseen so the next run retries."""
    res = llm_translate(batch, existing)
    log(f"LLM translated {len(res)}/{len(batch)}")
    out = []
    for i, b in enumerate(batch):
        t, d = res.get(i, ("", None))
        if t:
            b["en"], b["ne"] = (t, b["title"]) if b["lang"] == "ne" else (b["title"], t)
            b["dup"] = d
            out.append(b)
    return out


# ---------------- image ----------------
def font(files, size):
    for f in files:
        if pathlib.Path(f).exists():
            return ImageFont.truetype(str(f), size)
    return ImageFont.load_default(size=size)


def wrap(draw, text, fnt, width):
    lines, cur = [], ""
    for w in text.split():
        t = f"{cur} {w}".strip()
        if draw.textlength(t, font=fnt) <= width or not cur:
            cur = t
        else:
            lines.append(cur)
            cur = w
    return lines + ([cur] if cur else [])


def fit_text(draw, text, box, files, start=92, stop=40, spacing=1.22):
    x, y, w, h = box
    for size in range(start, stop - 1, -2):
        f = font(files, size)
        lines = wrap(draw, text, f, w)
        lh = int(size * spacing)
        if lh * len(lines) <= h and all(draw.textlength(l, font=f) <= w for l in lines):
            return f, lines, lh
    f = font(files, stop)
    return f, wrap(draw, text, f, w), int(stop * spacing)


def render(story, lang):
    """Headline only, centered in the template panel. Source + link go in the caption."""
    OUT.mkdir(exist_ok=True)
    img = Image.open(TEMPLATE).convert("RGB")
    d = ImageDraw.Draw(img)
    x, y, w, h = BOX
    f, lines, lh = fit_text(d, story[lang], BOX, FONT_BOLD)
    ty = y + (h - lh * len(lines)) // 2
    for i, line in enumerate(lines):
        lx = x + (w - d.textlength(line, font=f)) // 2
        d.text((lx, ty + i * lh), line, font=f, fill=TEXT_RGB)
    path = OUT / f"{int(time.time()*1000)}_{lang}.jpg"
    img.save(path, "JPEG", quality=92, optimize=True)  # IG accepts JPEG only
    return path


# ---------------- Meta ----------------
def graph(method, path, **data):
    data["access_token"] = os.environ["FB_PAGE_TOKEN"]
    files = data.pop("files", None)
    r = requests.request(method, f"{GRAPH}/{path}", data=data if method == "POST" else None,
                         params=data if method == "GET" else None, files=files, timeout=120)
    j = r.json()
    if r.status_code != 200 or "error" in j:
        raise RuntimeError(f"Graph {path}: {j}")
    return j


def post_facebook(img, text):
    with open(img, "rb") as fh:
        j = graph("POST", f"{os.environ['FB_PAGE_ID']}/photos", message=text,
                  files={"source": ("post.jpg", fh, "image/jpeg")})
    images = graph("GET", j["id"], fields="images")["images"]  # FB CDN copy = public URL for IG
    return j.get("post_id") or j["id"], max(images, key=lambda i: i["width"])["source"]


def post_instagram(img_url, text):
    ig = os.environ["IG_USER_ID"]
    cid = graph("POST", f"{ig}/media", image_url=img_url, caption=text)["id"]
    for _ in range(30):
        st = graph("GET", cid, fields="status_code")["status_code"]
        if st == "FINISHED":
            break
        if st in ("ERROR", "EXPIRED"):
            raise RuntimeError(f"IG container {st}")
        time.sleep(4)
    return graph("POST", f"{ig}/media_publish", creation_id=cid)["id"]


def captions(s, lang):
    summ = s["summary"] if s["lang"] == lang and s["summary"] else ""
    body = f"{s[lang]}\n\n{summ + chr(10) + chr(10) if summ else ''}"
    if lang == "ne":
        fb = f"{body}पूरा समाचार: {s['link']}\nस्रोत: {s['source']}\n\n{HASHTAGS_NE}"
        ig = f"{body}स्रोत: {s['source']}\nपूरा समाचार: {s['link']}\n\n{HASHTAGS_NE}"
    else:
        fb = f"{body}Read more: {s['link']}\nSource: {s['source']}\n\n{HASHTAGS_EN}"
        ig = f"{body}Source: {s['source']}\nFull story: {s['link']}\n\n{HASHTAGS_EN}"
    return fb, ig


def recent_page_links():
    """Links in the Page's last 50 posts, so a lost state.json can never cause a repost."""
    try:
        j = graph("GET", f"{os.environ['FB_PAGE_ID']}/posts", fields="message", limit=50)
        return set(re.findall(r"https?://\S+", " ".join(p.get("message", "") for p in j.get("data", []))))
    except Exception as ex:
        log(f"could not read Page posts: {ex!r}")
        return set()


# ---------------- main ----------------
def main():
    state = json.loads(STATE.read_text("utf-8")) if STATE.exists() else {}
    now = time.time()
    age_cut = now - MAX_AGE_H * 3600
    seen   = {k: v for k, v in state.get("seen", {}).items() if v > now - 2 * 86400}
    queue  = [q for q in state.get("queue", []) if q["ts"] > age_cut]
    posted = [p for p in state.get("posted", []) if p["ts"] > now - 7 * 86400]

    # 1. fetch + drop anything already seen / queued / posted
    with ThreadPoolExecutor(8) as ex:
        items = [i for batch in ex.map(fetch, FEEDS) for i in batch]
    known = set(seen) | {q["link"] for q in queue} | {p["link"] for p in posted}
    fresh = {}
    for it in sorted(items, key=lambda i: -i["ts"]):
        if it["link"] not in known:
            fresh.setdefault(it["link"], it)
    fresh = list(fresh.values())

    # 2. local same-language dedupe (free): repeats just boost the queued story's rank
    recent_posted = [p for p in posted if p["ts"] > now - 36 * 3600]
    new = []
    for it in fresh:
        pool = [q.get(it["lang"], "") for q in queue] + [p.get(it["lang"], "") for p in recent_posted]
        hit = next((q for q in queue if similar(it["title"], q.get(it["lang"], ""))), None)
        if hit or any(similar(it["title"], t) for t in pool) or any(
                n["lang"] == it["lang"] and similar(it["title"], n["title"]) for n in new):
            if hit:
                hit["hits"] += 1
            seen[it["link"]] = now
            continue
        new.append(it)
    log(f"{len(items)} fresh items, {len(fresh)} unseen, {len(new)} after local dedupe")

    # 3. ONE LLM request for up to LLM_BATCH new items (rest wait for next run)
    if new:
        batch = new[:LLM_BATCH]
        existing = [p["en"] for p in recent_posted][-40:] + [q["en"] for q in queue]
        n_posted = len([p["en"] for p in recent_posted][-40:])
        try:
            done = translate(batch, existing)
        except Exception as ex:
            log(f"{ex}; these {len(batch)} items will retry next run")
            done, batch = [], []
        for b in batch:
            seen[b["link"]] = now
        for i, b in enumerate(done):
            d, target = b.pop("dup", None), None
            if isinstance(d, str) and d.startswith("E") and d[1:].isdigit():
                k = int(d[1:])
                target = queue[k - n_posted] if n_posted <= k < len(existing) else "posted"
            elif d is not None and str(d).isdigit() and int(d) < batch.index(b):
                target = next((q for q in queue if q["link"] == batch[int(d)]["link"]), None)
            if target is None:  # safety net on English text
                target = next((q for q in queue if similar(b["en"], q["en"])), None) or \
                         ("posted" if any(similar(b["en"], p["en"]) for p in recent_posted) else None)
            if target == "posted":
                continue
            if isinstance(target, dict):
                target["hits"] += 1
                continue
            queue.append({**b, "hits": 1})

    # 4. post the top stories (more sources = more important, then trusted, then newest)
    queue.sort(key=lambda q: (-q["hits"], -q["weight"], -q["ts"]))
    fb_24 = sum(p.get("n_fb", 0) for p in posted if p["ts"] > now - 86400)
    ig_24 = sum(p.get("n_ig", 0) for p in posted if p["ts"] > now - 86400)
    log(f"queue {len(queue)} | last 24h: FB {fb_24}, IG {ig_24}")

    page_links = set() if DRY else recent_page_links()
    for _ in range(STORIES_PER_RUN):
        if not queue or fb_24 + 2 > FB_DAILY_CAP:
            break
        s = queue.pop(0)
        if s["link"] in page_links:
            log(f"already on Page, skipping: {s['en']}")
            posted.append({"ts": time.time(), "en": s["en"], "ne": s["ne"], "link": s["link"], "n_fb": 0, "n_ig": 0})
            continue
        rec = {"ts": time.time(), "en": s["en"], "ne": s["ne"], "link": s["link"], "n_fb": 0, "n_ig": 0}
        if not DRY:
            posted.append(rec)  # recorded BEFORE posting: a crash can never cause a repeat
            save(state, seen, queue, posted)
        for lang in ("en", "ne"):
            img = render(s, lang)
            fb_text, ig_text = captions(s, lang)
            if DRY:
                log(f"[DRY] {img}\n--- FB {lang} ---\n{fb_text}\n--- IG {lang} ---\n{ig_text}\n")
                continue
            try:
                pid, url = post_facebook(img, fb_text)
                rec["n_fb"] += 1; fb_24 += 1
                log(f"FB {lang} ok {pid}")
                if ig_24 + 1 <= IG_DAILY_CAP:
                    log(f"IG {lang} ok {post_instagram(url, ig_text)}")
                    rec["n_ig"] += 1; ig_24 += 1
            except Exception:
                log(f"POST FAIL {lang}:\n" + traceback.format_exc())
            save(state, seen, queue, posted)
            time.sleep(8)
    save(state, seen, queue, posted)


def save(state, seen, queue, posted):
    if DRY:
        return
    state.update(seen=seen, queue=queue, posted=posted, updated=int(time.time()))
    tmp = STATE.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, indent=1, ensure_ascii=False), "utf-8")
    os.replace(tmp, STATE)


if __name__ == "__main__":
    need = () if DRY else ("FB_PAGE_ID", "FB_PAGE_TOKEN", "IG_USER_ID")
    missing = [k for k in need if not os.getenv(k)]
    if missing:
        sys.exit(f"Missing env vars: {', '.join(missing)}")
    main()
