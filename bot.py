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
try:
    import nepali_datetime  # Bikram Sambat dates for the Nepali half of the stamp
except ImportError:
    nepali_datetime = None
import io
from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps

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
STORIES_PER_RUN = 1     # normal stories per run (each = 1 EN + 1 NE post); runs every ~10 min
BREAKING_PER_RUN = 3    # breaking stories skip the pacing and go out immediately, up to this many
BREAKING_PER_HOUR = 6   # hard cap so a busy news day can't turn into a flood of "breaking" posts
BREAKING_MAX_AGE_MIN = 90  # only fresh stories can count as breaking
ACTIVE_HOURS   = (4, 23)  # Nepal time: regular news only from 04:00 to 23:00, daily limits spread evenly
BREAKING_24H   = True     # breaking news may still post at night (uses the IG reserve below)
IG_BREAKING_RESERVE = 16  # IG posts (8 stories) kept free for breaking news in every rolling 24h
FB_BREAKING_RESERVE = 20  # FB posts (10 stories) kept free for breaking news
# How much of the day's regular budget each hour gets (Nepal time). Follows when Nepali
# audiences are online: morning scroll 6-9, lunch 12-2, and the big evening peak 6-10 PM.
HOUR_WEIGHT = {4: 0.3, 5: 0.6, 6: 1.0, 7: 1.3, 8: 1.3, 9: 1.1, 10: 1.1, 11: 1.1, 12: 1.2,
               13: 1.1, 14: 0.8, 15: 0.8, 16: 0.9, 17: 1.1, 18: 1.4, 19: 1.6, 20: 1.6,
               21: 1.3, 22: 0.9}
# Saturday and Sunday: people are online all day, so 9 AM to 10 PM gets a bigger share
WEEKEND = {9: 1.3, 10: 1.3, 11: 1.3, 12: 1.3, 13: 1.3, 14: 1.2, 15: 1.2, 16: 1.2,
           17: 1.3, 18: 1.4, 19: 1.6, 20: 1.6, 21: 1.6}
BREAKING = re.compile(r"\b(breaking|earthquake|quake|flood\w*|landslide\w*|avalanche|inundat\w*|"
                      r"killed|dead|death\w*|dies|died|fire|blaze|blast|explosion|crash\w*|accident|"
                      r"collapse\w*|missing|rescue\w*|evacuat\w*|curfew|resign\w*|arrest\w*|"
                      r"protest\w*|clash\w*|shoot\w*|attack\w*|emergency|alert|storm|"
                      r"defeat\w*|wins?)\b", re.I)
FB_DAILY_CAP   = 200    # FB posts per rolling 24h (no hard API cap; lower it if reach drops)
IG_DAILY_CAP   = 96     # IG API hard limit is 100 per rolling 24h
DUP_JACCARD    = 0.5    # word-overlap threshold for local duplicate detection
INCLUDE_SUMMARY = False  # False: caption = headline + source + link only (no copied article text)
HASHTAGS_EN    = "#Nepal #NepalNews #NepalInBrief"
HASHTAGS_NE    = "#नेपाल #समाचार #NepalInBrief"

# Outlets never to post from (matched anywhere in the source name, case-insensitive).
# Covers stories that arrive via Google News under the publisher's name.
SOURCE_BLOCKLIST = ["nepalnews"]   # nepalnews.com: undated / very late updates


def blocked(source):
    return any(b in (source or "").lower() for b in SOURCE_BLOCKLIST)


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
    ("Khabarhub",       "https://khabarhub.com/feed",                     False, 3),
    ("Gorkhapatra",     "https://gorkhapatraonline.com/rss",              False, 3),
    ("Annapurna Post",  "https://annapurnapost.com/rss",                  False, 3),
    ("Baahrakhari",     "https://baahrakhari.com/feed",                   False, 2),
    ("Ujyaalo",         "https://ujyaaloonline.com/feed",                 False, 2),
    ("Deshsanchar",     "https://deshsanchar.com/feed",                   False, 2),
    ("Lokaantar",       "https://lokaantar.com/feed",                     False, 2),
    # Nepal, English
    ("Kathmandu Post",  "https://kathmandupost.com/rss",                  False, 3),
    ("Onlinekhabar EN", "https://english.onlinekhabar.com/feed",          False, 3),
    ("Himalayan Times", "https://thehimalayantimes.com/rssFeed/15",       False, 3),
    ("Rising Nepal",    "https://risingnepaldaily.com/rss",               False, 2),
    ("Khabarhub EN",    "https://english.khabarhub.com/feed",             False, 2),
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
BOX       = (100, 520, 1054, 400)              # headline area inside the panel: left, top, width, height
STAMP_Y   = 482                                # centre line of the date pill, just under the LATEST ribbon
TEXT_RGB  = (255, 255, 255)
PHOTO_LAYOUT = "background"   # "background" (translucent photo behind the headline) or "off"
PHOTO_OPACITY = 0.42          # how visible the photo is behind the headline (0 = hidden, 1 = full)
PHOTO_TOP  = 515              # photo starts below the LATEST ribbon + date pill, fading in over PHOTO_FADE px
PHOTO_FADE = 70
TEXT_STROKE = 3               # thin black outline around the white headline
PHOTO_BLOCKLIST = set()       # outlet names whose photos must never be used, e.g. {"Kathmandu Post"}
PANEL     = (49, 424, 1205, 954)   # the template's dark panel (where the photo goes)
FONT_BOLD = [HERE / "assets" / "fonts" / "headline.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"]
# ==========================================

STATE = HERE / "state.json"
OUT   = HERE / "out"
NPT   = timezone(timedelta(hours=5, minutes=45))
# dry run: render + print only. Runs from any branch other than main are always dry (preview branches).
DRY   = os.getenv("DRY_RUN") == "1" or os.getenv("GITHUB_REF_NAME", "main") != "main"
UA    = {"User-Agent": "Mozilla/5.0 (NepalInBrief bot)"}
URL_DATE = re.compile(r"/(20\d\d)/(\d\d)/(\d\d)/")
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
IMG_TAG = re.compile(r"""<img[^>]+src=["']([^"']+)""", re.I)
OG_IMAGE = re.compile(r"""<meta[^>]+(?:property|name)=["'](?:og:image|twitter:image)["'][^>]+content=["']([^"']+)"""
                      r"""|<meta[^>]+content=["']([^"']+)["'][^>]+(?:property|name)=["'](?:og:image|twitter:image)["']""", re.I)


BROWSER_UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                            "(KHTML, like Gecko) Chrome/128.0 Safari/537.36"}
RAW_ITEM = re.compile(r"<item\b.*?</item>", re.S | re.I)
RAW_LINK = re.compile(r"<link>\s*(?:<!\[CDATA\[)?\s*(.*?)\s*(?:\]\]>)?\s*</link>", re.S | re.I)
RAW_IMG = re.compile(r"<image>\s*(?:<!\[CDATA\[)?\s*(https?://[^<\]\s]+)", re.I)


def raw_images(xml):
    """Some feeds (e.g. Onlinekhabar) put a plain <image> tag in each item, which feedparser drops."""
    out = {}
    for block in RAW_ITEM.findall(xml):
        lk, im = RAW_LINK.search(block), RAW_IMG.search(block)
        if lk and im:
            out[norm_link(html.unescape(lk.group(1)))] = html.unescape(im.group(1))
    return out


def feed_image(e):
    """The thumbnail the feed itself publishes for this item (no extra request)."""
    for key in ("media_content", "media_thumbnail"):
        for m in e.get(key) or []:
            if m.get("url"):
                return m["url"]
    for enc in e.get("enclosures") or []:
        if str(enc.get("type", "")).startswith("image") and enc.get("href"):
            return enc["href"]
    for c in (e.get("content") or []) + [{"value": e.get("summary", "")}]:
        m = IMG_TAG.search(c.get("value") or "")
        if m:
            return html.unescape(m.group(1))
    return None


def load_photo(story):
    """Thumbnail from the feed, else the article's og:image (the link-preview image). None if unusable.
    Always logs what happened, so a post without a photo can be explained from the Actions log."""
    tag = f"photo ({story['source']})"
    if PHOTO_LAYOUT == "off" or story["source"] in PHOTO_BLOCKLIST:
        return None
    if "news.google.com" in story["link"]:
        log(f"{tag}: none, Google News link (by design)")
        return None
    url, where = story.get("img"), "feed"
    try:
        if not url:
            where = "og:image"
            page = requests.get(story["link"], timeout=15, headers=BROWSER_UA).text[:400000]
            m = OG_IMAGE.search(page)
            url = html.unescape(m.group(1) or m.group(2)) if m else None
        if not url:
            log(f"{tag}: none, no image in feed or article page")
            return None
        r = requests.get(url, timeout=15, headers={**BROWSER_UA, "Referer": story["link"]})
        r.raise_for_status()
        im = Image.open(io.BytesIO(r.content)).convert("RGB")
        if min(im.size) < 250:
            log(f"{tag}: none, image too small {im.size}")
            return None
        log(f"{tag}: ok from {where} {im.size}")
        return im
    except Exception as ex:
        log(f"{tag}: none, {where} failed: {ex!r}"[:300])
        return None


def fetch(feed):
    name, url, needs_nepal, weight = feed
    try:
        r = requests.get(url, timeout=20, headers=UA)
        r.raise_for_status()
        entries = feedparser.parse(r.content).entries
        raw_imgs = raw_images(r.content.decode("utf-8", "ignore"))
    except Exception as ex:
        log(f"FEED FAIL {name}: {ex!r}")
        return []
    now, out = time.time(), []
    for e in entries:
        pub = e.get("published_parsed") or e.get("updated_parsed")
        link = norm_link(e.get("link"))
        m = URL_DATE.search(link)
        if m and now - calendar.timegm((int(m[1]), int(m[2]), int(m[3]), 23, 59, 0)) > 86400:
            continue  # URL says it's from before yesterday: stale, whatever the feed claims
        # undated items would otherwise look brand new on every run and crowd out other sources
        ts = calendar.timegm(pub) if pub else now - 4 * 3600
        if now - ts > MAX_AGE_H * 3600:
            continue
        title, summary, src = clean(e.get("title")), clean(e.get("summary")), name
        if name.startswith("Google News"):  # "Headline - Publisher", summary is just link soup
            src = (e.get("source") or {}).get("title") or name
            title, summary = re.sub(rf"\s+-\s+{re.escape(src)}$", "", title), ""
        if needs_nepal and not NEPAL.search(f"{title} {summary}"):
            continue
        if blocked(src):
            continue
        if title and link:
            out.append({"title": title, "summary": shorten(summary, 220), "link": link,
                        "source": src, "ts": ts, "weight": weight,
                        "img": feed_image(e) or raw_imgs.get(link),
                        "lang": "ne" if DEVA.search(title) else "en"})
    log(f"{name}: {len(out)} fresh")
    return out


def round_robin(items, n):
    """Take items source by source (A, B, C, A, B, C...) so no single outlet fills the batch."""
    by = {}
    for it in items:  # items are already newest first
        by.setdefault(it["source"], []).append(it)
    out = []
    while len(out) < n and any(by.values()):
        for src in by:
            if by[src] and len(out) < n:
                out.append(by[src].pop(0))
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


NE_DIGITS = str.maketrans("0123456789", "०१२३४५६७८९")
NE_MONTHS = ["बैशाख", "जेठ", "असार", "साउन", "भदौ", "असोज", "कात्तिक", "मंसिर", "पुस", "माघ", "फागुन", "चैत"]


def date_stamp(ts):
    """'25 Sep 2026, 12:00 PM   |   २०८३ असोज ९, दिउँसो १२:००' in Nepal time."""
    t = datetime.fromtimestamp(ts, NPT)
    en = t.strftime("%d %b %Y, %I:%M %p").lstrip("0")
    if nepali_datetime is None:
        return en
    b = nepali_datetime.datetime.from_datetime_datetime(t.replace(tzinfo=None))
    part = "बिहान" if 4 <= t.hour < 12 else "दिउँसो" if t.hour < 17 else "साँझ" if t.hour < 20 else "राति"
    ne = f"{b.year} {NE_MONTHS[b.month - 1]} {b.day}, {part} {t.hour % 12 or 12}:{t.minute:02d}"
    return f"{en}   |   {ne.translate(NE_DIGITS)}"


def place_photo(img, photo):
    """Translucent news photo behind the headline. The top of the panel (LATEST ribbon + date pill)
    stays clean; the photo fades in below it. Border and red corners stay on top."""
    size = (PANEL[2] - PANEL[0], PANEL[3] - PANEL[1])
    ph = ImageOps.fit(photo, size).filter(ImageFilter.GaussianBlur(1.2))
    panel = img.crop(PANEL)
    # vertical alpha: 0 above PHOTO_TOP, fading up to PHOTO_OPACITY
    top = PHOTO_TOP - PANEL[1]
    col = [0 if y < top else int(255 * PHOTO_OPACITY * min(1, (y - top) / PHOTO_FADE)) for y in range(size[1])]
    alpha = Image.new("L", (1, size[1]))
    alpha.putdata(col)
    alpha = alpha.resize(size)
    # never paint over the template's own details (panel border, red corner accents)
    details = panel.convert("L").point(lambda v: 255 if v > 55 else 0).filter(ImageFilter.MaxFilter(5))
    alpha = Image.composite(Image.new("L", size, 0), alpha, details)
    img.paste(Image.composite(ph, panel, alpha), PANEL[:2])
    return (100, 540, 1054, 370), (1150, 928)


def render(story, lang):
    """Headline in the template panel, optional news photo, date pill. Source + link go in the caption."""
    OUT.mkdir(exist_ok=True)
    img = Image.open(TEMPLATE).convert("RGB")
    box, credit_at = BOX, None
    photo = story.get("_photo")
    if photo is not None and PHOTO_LAYOUT != "off":
        box, credit_at = place_photo(img, photo)
    d = ImageDraw.Draw(img)
    x, y, w, h = box
    f, lines, lh = fit_text(d, story[lang], box, FONT_BOLD)
    ty = y + (h - lh * len(lines)) // 2
    for i, line in enumerate(lines):
        lx = x + (w - d.textlength(line, font=f)) // 2
        d.text((lx, ty + i * lh), line, font=f, fill=TEXT_RGB,
               stroke_width=TEXT_STROKE, stroke_fill=(0, 0, 0))

    # date pill under the LATEST ribbon (same post time on the EN and NE image)
    if credit_at:  # small, 50% transparent photo credit
        layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
        ImageDraw.Draw(layer).text(credit_at, f"Photo: {story['source']}", font=font(FONT_BOLD, 17),
                                   fill=(255, 255, 255, 128), anchor="rs")
        img = Image.alpha_composite(img.convert("RGBA"), layer).convert("RGB")
        d = ImageDraw.Draw(img)

    stamp = date_stamp(story.get("post_ts") or time.time())
    sf = font(FONT_BOLD, 28)
    cx, sw = BOX[0] + BOX[2] // 2, d.textlength(stamp, font=sf)
    d.rounded_rectangle([cx - sw / 2 - 24, STAMP_Y - 21, cx + sw / 2 + 24, STAMP_Y + 21],
                        radius=21, fill=(8, 14, 32), outline=(220, 30, 45), width=2)
    d.text((cx, STAMP_Y), stamp, font=sf, fill=TEXT_RGB, anchor="mm")
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
    summ = s["summary"] if INCLUDE_SUMMARY and s["lang"] == lang and s["summary"] else ""
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
    queue  = [q for q in state.get("queue", []) if q["ts"] > age_cut and not blocked(q.get("source"))]
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
        batch = round_robin(new, LLM_BATCH)
        # keep the dedupe context small: runs are frequent, so this is what dominates token use
        existing = [p["en"] for p in recent_posted][-15:] + [q["en"] for q in queue][-15:]
        n_posted = len([p["en"] for p in recent_posted][-15:])
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

    # 4. post the top stories: most-covered first, then the outlet we've used least recently
    #    (so the feed mixes Onlinekhabar, Setopati, Ratopati, Nagarik, KP...), then trusted, then newest
    recent_src = [p.get("source") for p in posted][-8:]
    fb_24 = sum(p.get("n_fb", 0) for p in posted if p["ts"] > now - 86400)
    ig_24 = sum(p.get("n_ig", 0) for p in posted if p["ts"] > now - 86400)
    log(f"queue {len(queue)} | last 24h: FB {fb_24}, IG {ig_24}")

    def is_breaking(q):  # fresh AND (several outlets on it at once, or an urgent keyword)
        fresh = time.time() - q["ts"] <= BREAKING_MAX_AGE_MIN * 60
        return fresh and (q["hits"] >= 3 or bool(BREAKING.search(q["en"])))

    brk_hour = sum(1 for p in posted if p.get("brk") and p["ts"] > time.time() - 3600)

    # Even pacing across the active window: by X% of the window, at most X% of the day's budget
    # may be used, so the limits can't run out at noon and leave the evening empty.
    t = datetime.now(NPT)
    start_h, end_h = ACTIVE_HOURS
    day_start = t.replace(hour=start_h, minute=0, second=0, microsecond=0).timestamp()
    active = start_h <= t.hour < end_h
    weights = {**HOUR_WEIGHT, **(WEEKEND if t.weekday() in (5, 6) else {})}  # 5 = Sat, 6 = Sun
    w = [weights.get(h, 0) for h in range(start_h, end_h)]
    done = sum(w[: max(0, t.hour - start_h)])
    if active:
        done += w[t.hour - start_h] * (t.minute * 60 + t.second) / 3600
    frac = min(1.0, done / sum(w)) if t.hour >= start_h else 0.0   # share of the day's budget usable by now
    # "today" also covers the quiet hours before the window, so night-time breaking posts
    # are paid for out of the same day's budget
    since = day_start - (24 - (end_h - start_h)) * 3600
    fb_today = sum(p.get("n_fb", 0) for p in posted if p["ts"] >= since)
    ig_today = sum(p.get("n_ig", 0) for p in posted if p["ts"] >= since)
    fb_budget = (FB_DAILY_CAP - FB_BREAKING_RESERVE) * frac + 2   # posts allowed so far (+1 story slack)
    ig_budget = (IG_DAILY_CAP - IG_BREAKING_RESERVE) * frac + 2
    normal_ok = active and fb_today + 2 <= fb_budget and fb_24 + 2 <= FB_DAILY_CAP - FB_BREAKING_RESERVE
    ig_normal_ok = ig_today + 2 <= ig_budget and ig_24 + 2 <= IG_DAILY_CAP - IG_BREAKING_RESERVE
    log(f"{'active' if active else 'quiet hours'} | today FB {fb_today}/{fb_budget:.0f}, "
        f"IG {ig_today}/{ig_budget:.0f}")
    if DRY:  # preview: top 4 stories from different outlets, rendered in EN + NE
        picks, used = [], set()
        for q in sorted(queue, key=lambda q: (-q["hits"], -q["weight"], -q["ts"])):
            if q["source"] not in used and "news.google.com" not in q["link"]:
                picks.append(q); used.add(q["source"])
            if len(picks) == 4:
                break
        for q in picks:
            q["post_ts"] = time.time()
            q["_photo"] = load_photo(q)
            log(f"[PREVIEW] {q['source']}: photo {'found' if q['_photo'] is not None else 'NOT found'} | {q['en']}")
            for lang in ("en", "ne"):
                log(f"   {lang}: {render(q, lang)}")
        return

    page_links = set() if DRY else recent_page_links()
    n_breaking = n_normal = 0
    while queue and fb_24 + 2 <= FB_DAILY_CAP:
        br = [q for q in queue if is_breaking(q)]
        if (br and (active or BREAKING_24H) and n_breaking < BREAKING_PER_RUN
                and brk_hour + n_breaking < BREAKING_PER_HOUR):
            pool, breaking = br, True
        elif normal_ok and n_normal < STORIES_PER_RUN:
            pool, breaking = queue, False
        else:
            break
        s = min(pool, key=lambda q: (-q["hits"], recent_src.count(q["source"]), -q["weight"], -q["ts"]))
        queue.remove(s)
        if breaking:
            n_breaking += 1
        else:
            n_normal += 1
        recent_src.append(s["source"])
        if s["link"] in page_links:
            log(f"already on Page, skipping: {s['en']}")
            if breaking:  # a skip doesn't use up this run's slot
                n_breaking -= 1
            else:
                n_normal -= 1
            posted.append({"ts": time.time(), "en": s["en"], "ne": s["ne"], "link": s["link"],
                           "source": s["source"], "n_fb": 0, "n_ig": 0})
            continue
        rec = {"ts": time.time(), "en": s["en"], "ne": s["ne"], "link": s["link"],
               "source": s["source"], "n_fb": 0, "n_ig": 0, "brk": breaking}
        if not DRY:
            posted.append(rec)  # recorded BEFORE posting: a crash can never cause a repeat
            save(state, seen, queue, posted)
        s["post_ts"] = time.time()
        s["_photo"] = load_photo(s)
        use_ig = breaking or ig_normal_ok  # decide once per story, so EN and NE go together
        if use_ig:
            ig_today += 2
            ig_normal_ok = ig_today + 2 <= ig_budget and ig_24 + 4 <= IG_DAILY_CAP - IG_BREAKING_RESERVE
        for lang in ("en", "ne"):
            img = render(s, lang)
            fb_text, ig_text = captions(s, lang)
            if DRY:
                log(f"[DRY] {img}\n--- FB {lang} ---\n{fb_text}\n--- IG {lang} ---\n{ig_text}\n")
                continue
            try:
                pid, url = post_facebook(img, fb_text)
                rec["n_fb"] += 1; fb_24 += 1
                log(f"FB {lang} ok {pid}{' [BREAKING]' if breaking else ''}")
                if use_ig and ig_24 + 1 <= IG_DAILY_CAP - (0 if breaking else IG_BREAKING_RESERVE):
                    log(f"IG {lang} ok {post_instagram(url, ig_text)}")
                    rec["n_ig"] += 1; ig_24 += 1
            except Exception:
                log(f"POST FAIL {lang}:\n" + traceback.format_exc())
            save(state, seen, queue, posted)
            time.sleep(8)
        s.pop("_photo", None)
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
