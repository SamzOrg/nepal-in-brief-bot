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
# Translation + duplicate flags. Full batches: Groq first, Gemini if Groq fails. Small urgent calls:
# Gemini first, Groq if Gemini fails (spreads the daily load over both free tiers).
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
LLM_MIN_BATCH  = 20     # wait for this many new headlines before a full AI call...
LLM_MAX_WAIT_MIN = 30   # ...or until the oldest waiting one has waited this long.
                        # Critical-looking headlines skip the wait via a small "urgent" call (below).
LLM_MAX_OUT    = 2500   # reserved answer tokens. Groq counts prompt + this against its 8K/min limit
# Headlines critical enough to translate right away in a small separate call (EN + NE words)
CRITICAL = re.compile(r"\b(breaking|earthquakes?|quakes?|tremors?|floods?|flooded|flooding|flash[- ]floods?|"
                      r"landslides?|avalanches?|glof|cloudbursts?|killed|dead|deaths?|dies|died|explosion|"
                      r"blast|curfew|emergency|collapse\w*|defeat\w*|wins?)\b"
                      r"|भूकम्प|बाढी|पहिरो|हिमपहिरो|मृत्यु|मृतक|विस्फोट|कर्फ्यु|संकटकाल|हरायो|जित्यो", re.I)
URGENT_MAX = 4          # headlines per urgent call
STORIES_PER_RUN = 1     # normal stories per run (each = 1 bilingual post on FB and on IG); runs every ~10 min
BREAKING_PER_RUN = 1    # breaking stories skip the pacing and go out immediately, up to this many
NORMAL_GAP_MIN = 30     # at most one regular (non-breaking) story every 30 minutes
NORMAL_MIN_IMPACT = 3   # regular stories need AI impact >= 3 (1-5 scale); lower ones are never posted
RESUME_LEAD_MIN = 45    # when posting is paused, start collecting again this long before it resumes
MAX_STORIES_PER_RUN = 1 # never more than this many stories in one run (no bursts: Meta flags them as spam)
BLOCK_COOLDOWN_H = 5    # Meta spam block (error 368): stop posting this long, doubled if it happens again within 48h
BREAKING_PER_HOUR = 3   # hard cap so a busy news day can't turn into a flood of "breaking" posts
BREAKING_MAX_AGE_MIN = 90  # only fresh stories can count as breaking
ACTIVE_HOURS   = (4, 23)  # Nepal time: regular news only from 04:00 to 23:00, daily limits spread evenly
BREAKING_24H   = True     # breaking news may still post at night (uses the IG reserve below)
IG_BREAKING_RESERVE = 8   # IG posts (stories) kept free for breaking news in every rolling 24h
FB_BREAKING_RESERVE = 8   # FB posts (stories) kept free for breaking news
# How much of the day's regular budget each hour gets (Nepal time). Follows when Nepali
# audiences are online: morning scroll 6-9, lunch 12-2, and the big evening peak 6-10 PM.
HOUR_WEIGHT = {4: 0.3, 5: 0.6, 6: 1.0, 7: 1.3, 8: 1.3, 9: 1.1, 10: 1.1, 11: 1.1, 12: 1.2,
               13: 1.1, 14: 0.8, 15: 0.8, 16: 0.9, 17: 1.1, 18: 1.4, 19: 1.6, 20: 1.6,
               21: 1.3, 22: 0.9}
# Saturday and Sunday: people are online all day, so 9 AM to 10 PM gets a bigger share
WEEKEND = {9: 1.3, 10: 1.3, 11: 1.3, 12: 1.3, 13: 1.3, 14: 1.2, 15: 1.2, 16: 1.2,
           17: 1.3, 18: 1.4, 19: 1.6, 20: 1.6, 21: 1.6}
BREAKING = re.compile(
    r"\b(breaking|"
    # disasters and weather
    r"earthquakes?|quakes?|tremors?|aftershocks?|floods?|flooded|flooding|flash[- ]floods?|"
    r"landslides?|mudslides?|debris flows?|avalanches?|inundat\w*|cloudbursts?|glof|glacial lake|"
    r"outburst|heavy rain\w*|downpours?|storms?|hailstorms?|snowstorms?|cyclones?|lightning|"
    r"wildfires?|forest fires?|fire|blaze|drought|"
    # roads, travel and services
    r"closed|closures?|shut|shutdown|blocked|blockade|obstructed|halted|suspended|disrupted|"
    r"swept away|washed away|cut off|stranded|"
    # casualties and incidents
    r"killed|dead|death\w*|dies|died|drown\w*|injured|missing|rescue\w*|evacuat\w*|"
    r"blast|explosion|crash\w*|accident|collapse\w*|"
    # security and politics
    r"curfew|resign\w*|arrest\w*|protest\w*|clash\w*|shoot\w*|attack\w*|emergency|alert|"
    # sports results
    r"defeat\w*|wins?)\b", re.I)
FB_DAILY_CAP   = 0      # optional FB posts-per-24h cap; 0 = off (pacing below + the Meta-block pause keep volume safe)
IG_DAILY_CAP   = 96     # IG API hard limit is 100 per rolling 24h
DUP_JACCARD    = 0.5    # word-overlap threshold for local duplicate detection
INCLUDE_SUMMARY = False  # False: caption = headline + source + link only (no copied article text)
HASHTAGS_EN    = "#NepalInBrief #NepalNews"   # brand tags on every post
MAX_HASHTAGS   = 5      # Instagram only counts 5 hashtags per post; more can hurt reach (also on Facebook)
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
    ("News24 Nepal",    "https://news24nepal.tv/feed/",                   False, 3),
    # Nepal, English
    ("Kathmandu Post",  "https://kathmandupost.com/rss",                  False, 3),
    ("Onlinekhabar EN", "https://english.onlinekhabar.com/feed",          False, 3),
    ("Himalayan Times", "https://thehimalayantimes.com/rssFeed/15",       False, 3),
    ("Rising Nepal",    "https://risingnepaldaily.com/rss",               False, 2),
    ("Khabarhub EN",    "https://english.khabarhub.com/feed",             False, 2),
    # myRepublica has no RSS feed, so its stories come via a Google News search limited to its site
    ("Google News Republica", "https://news.google.com/rss/search?q=site:myrepublica.nagariknetwork.com+when:1d"
                              "&hl=en-US&gl=US&ceid=US:en",               False, 3),
    # International, only items that mention Nepal
    ("Google News",     "https://news.google.com/rss/search?q=Nepal+when:1d&hl=en-US&gl=US&ceid=US:en", True, 2),
    ("Google News IN",  "https://news.google.com/rss/search?q=Nepal+when:1d&hl=en-IN&gl=IN&ceid=IN:en", True, 2),
    ("Al Jazeera",      "https://www.aljazeera.com/xml/rss/all.xml",      True, 3),
    ("BBC Asia",        "https://feeds.bbci.co.uk/news/world/asia/rss.xml", True, 3),
    ("The Guardian",    "https://www.theguardian.com/world/nepal/rss",    True, 3),
]

# ---- image ----
HERE      = pathlib.Path(__file__).parent
TEXT_STROKE = 3               # outline around the headline (black on dark, white on the white template)
PHOTO_LAYOUT = "background"   # "background" (translucent news photo behind the headlines) or "off"
PHOTO_FADE = 60               # px over which the photo fades in below the date pill
PHOTO_BLOCKLIST = set()       # outlet names whose photos must never be used, e.g. {"Kathmandu Post"}
FONT_BOLD = [HERE / "assets" / "fonts" / "headline.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"]
NAVY      = (14, 28, 64)
THEME     = "alternate"       # "dark", "white", or "alternate" (dark and white take turns, story by story)
HEADLINE_MAX_PX = 76          # biggest headline size; long headlines shrink to fit (same size for EN and NE)
HEADLINE_PAD_X  = 90          # space between the headline and the panel's left/right edge
HEADLINE_GAP    = 50          # space between the English and Nepali headline (the red divider sits here)
DATE_PX         = 28          # font size of the date pill under the ribbon
HEADLINE_LINE_H = 1.30        # line height as a multiple of the font size
# One post per story: English headline on top, Nepali below. Panel = the template's box
# (left, top, right, bottom); ribbon = bottom of the LATEST/BREAKING ribbon at the centre.
STYLES = {
    "dark":  {"template": HERE / "assets" / "template.jpg",
              "breaking_template": HERE / "assets" / "template_breaking.jpg",
              "panel": (47, 352, 1208, 950), "ribbon": 360,
              "breaking_panel": (47, 372, 1208, 972), "breaking_ribbon": 388,
              "text": (255, 255, 255), "text_ne": (255, 206, 84), "stroke": (0, 0, 0),
              "credit": (255, 255, 255, 128),
              # layout "C": max 66px text, 115px side space, 56px between languages, date 24px
              "max_px": 66, "pad_x": 115, "gap": 56, "date_px": 24, "line_h": 1.34,
              "dark_panel": True, "opacity": 0.55, "stroke_w": TEXT_STROKE},
    "white": {"template": HERE / "assets" / "template_ne.jpg",
              "breaking_template": HERE / "assets" / "template_ne_breaking.jpg",
              "panel": (38, 403, 1218, 942), "ribbon": 400,
              "breaking_panel": (38, 408, 1218, 942), "breaking_ribbon": 411,
              "text": (20, 20, 24), "text_ne": (110, 14, 30), "stroke": (255, 255, 255),
              "credit": (14, 28, 64, 140),
              # layout "F": max 60px text, 130px side space, 62px between languages, date 22px
              "max_px": 60, "pad_x": 130, "gap": 62, "date_px": 22, "line_h": 1.38,
              "dark_panel": False, "opacity": 0.45, "stroke_w": 2},
}
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


STOP = {"the", "and", "for", "with", "from", "after", "over", "into", "amid", "says", "said", "will",
        "has", "have", "been", "its", "their", "his", "her", "new", "today", "nepal", "nepali",
        "nepalese", "news", "update", "latest", "event", "photos", "video"}


def stem(w):
    if len(w) <= 4:
        return w
    if w.endswith(("ches", "shes", "sses", "xes")):
        return w[:-2]
    for suf in ("ing", "ed", "s"):
        if len(w) > len(suf) + 3 and w.endswith(suf) and not w.endswith("ss"):
            return w[: -len(suf)]
    return w


def key_words(s):
    return {stem(w) for w in words(s) if w not in STOP}


def similar(a, b):
    """Same story? Either the old word-overlap test, or 2+ shared key words (ignoring 'Nepal', 'the'...,
    and matching defeat/defeats/defeated) covering at least half of the shorter headline, one of
    them a longer name-like word (e.g. 'afghanistan', 'landslide')."""
    wa, wb = words(a), words(b)
    if wa and wb and len(wa & wb) / len(wa | wb) >= DUP_JACCARD:
        return True
    ka, kb = key_words(a), key_words(b)
    shared = ka & kb
    return (len(shared) >= 2 and len(shared) / max(1, min(len(ka), len(kb))) >= 0.5
            and any(len(w) >= 6 for w in shared))


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
- "s": impact for people in Nepal, 1-5. 5 = national emergency or major disaster, many deaths, fall of
  government. 4 = important national news: deaths, major decisions, highways or services shut, big Nepal
  sports results. 3 = notable news worth sharing. 2 = routine or local. 1 = trivial, photo features,
  events, or foreign news with little bearing on Nepal.
- "h": 2-4 hashtags for the story's key topic, places, people or organisations, without "#".
  CamelCase English (e.g. "Landslide", "PrithviHighway", "Chitwan"); one may be Nepali (e.g. "पहिरो").

Respond with JSON only: {{"r": [{{"i": 0, "t": "...", "d": null, "s": 3, "h": ["Landslide", "Chitwan"]}}]}}
with one entry per new item.

EXISTING:
{existing}

NEW:
{new}
"""


def llm_translate(batch, existing, prefer_gemini=False):
    prompt = PROMPT.format(
        existing="\n".join(f"E{i}: {t}" for i, t in enumerate(existing)) or "(none)",
        new="\n".join(f"{i} [{b['lang']}] {b['title']}" for i, b in enumerate(batch)))
    order = PROVIDERS[::-1] if prefer_gemini else PROVIDERS  # spread load across both free tiers
    for name, url, key_env, model, extra in order:
        key = os.getenv(key_env)
        if not key:
            continue
        try:
            r = requests.post(url, headers={"Authorization": f"Bearer {key}"}, timeout=90,
                              json={"model": model, "temperature": 0.1, "max_completion_tokens": LLM_MAX_OUT,
                                    "response_format": {"type": "json_object"},
                                    "messages": [{"role": "user", "content": prompt}], **extra})
            if r.status_code != 200:
                raise RuntimeError(f"{r.status_code}: {r.text[:200]}")
            text = r.json()["choices"][0]["message"]["content"]
            text = text[text.find("{"):text.rfind("}") + 1]  # tolerate ```json fences
            rows = json.loads(text)["r"]
            log(f"LLM ok via {name}")
            return {int(x["i"]): (clean(x.get("t", "")), x.get("d"), x.get("s"), x.get("h"))
                    for x in rows if "i" in x}
        except Exception as ex:
            log(f"LLM {name} failed: {ex!r}")
    raise RuntimeError("all LLM providers failed")


def translate(batch, existing, prefer_gemini=False):
    """Raises if both models fail; caller then leaves the items unseen so the next run retries."""
    res = llm_translate(batch, existing, prefer_gemini)
    log(f"LLM translated {len(res)}/{len(batch)}")
    out = []
    for i, b in enumerate(batch):
        t, d, imp, tags = res.get(i, ("", None, None, None))
        if t:
            b["en"], b["ne"] = (t, b["title"]) if b["lang"] == "ne" else (b["title"], t)
            b["dup"] = d
            try:
                b["imp"] = min(5, max(1, int(imp)))
            except (TypeError, ValueError):
                b["imp"] = None  # unknown: treated as 3
            b["tags"] = [clean_tag(x) for x in tags if clean_tag(x)][:4] if isinstance(tags, list) else []
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


def place_photo(img, photo, st, panel_box, photo_top):
    """Translucent news photo behind the headlines. The top of the panel (ribbon + date pill)
    stays clean; the photo fades in below it. Border and red corners stay on top."""
    size = (panel_box[2] - panel_box[0], panel_box[3] - panel_box[1])
    ph = ImageOps.fit(photo, size).filter(ImageFilter.GaussianBlur(1.2))
    panel = img.crop(panel_box)
    # vertical alpha: 0 above photo_top, fading up to PHOTO_OPACITY
    top = photo_top - panel_box[1]
    col = [0 if y < top else int(255 * st["opacity"] * min(1, (y - top) / PHOTO_FADE)) for y in range(size[1])]
    alpha = Image.new("L", (1, size[1]))
    alpha.putdata(col)
    alpha = alpha.resize(size)
    # never paint over the template's own details (panel border, red corner accents)
    if st["dark_panel"]:
        details = panel.convert("L").point(lambda v: 255 if v > 55 else 0)
    else:  # white panel: details are the coloured / darker pixels
        hsv_s = panel.convert("HSV").split()[1].point(lambda v: 255 if v > 70 else 0)
        dark = panel.convert("L").point(lambda v: 255 if v < 200 else 0)
        details = Image.composite(Image.new("L", size, 255), dark, hsv_s)
    details = details.filter(ImageFilter.MaxFilter(5))
    alpha = Image.composite(Image.new("L", size, 0), alpha, details)
    # keep the photo inside the panel's rounded corners
    shape = Image.new("L", size, 0)
    ImageDraw.Draw(shape).rounded_rectangle([4, 0, size[0] - 5, size[1] - 5], radius=26, fill=255)
    alpha = Image.composite(alpha, Image.new("L", size, 0), shape)
    img.paste(Image.composite(ph, panel, alpha), panel_box[:2])


def balanced_wrap(draw, text, fnt, width):
    """Same number of lines as a greedy wrap, but evenly filled (no lone word on the last line)."""
    n = len(wrap(draw, text, fnt, width))
    lo, hi = width // 2, width
    while lo < hi:
        mid = (lo + hi) // 2
        if len(wrap(draw, text, fnt, mid)) <= n:
            hi = mid
        else:
            lo = mid + 1
    return wrap(draw, text, fnt, lo)


def render(story, theme="dark"):
    """One image per story: English headline on top, Nepali below, same size, optional translucent
    news photo behind, date pill under the ribbon. Source + link go in the caption."""
    OUT.mkdir(exist_ok=True)
    st = STYLES[theme]
    brk = bool(story.get("_breaking")) and st["breaking_template"].exists()
    img = Image.open(st["breaking_template"] if brk else st["template"]).convert("RGB")
    panel = st["breaking_panel"] if brk else st["panel"]
    l, top, r, b = panel
    pill_y = (st["breaking_ribbon"] if brk else st["ribbon"]) + 40
    pad_x = st.get("pad_x", HEADLINE_PAD_X)
    x, w = l + pad_x, (r - l) - 2 * pad_x                     # side padding
    y0, y1 = pill_y + 21 + 45, b - 55            # below the date pill, above the panel bottom
    gap = st.get("gap", HEADLINE_GAP)            # space between the two languages (divider sits here)
    line_h = st.get("line_h", HEADLINE_LINE_H)
    date_px = st.get("date_px", DATE_PX)

    credit = False
    photo = story.get("_photo")
    if photo is not None and PHOTO_LAYOUT != "off":
        place_photo(img, photo, st, panel, pill_y + 30)
        credit = True
    d = ImageDraw.Draw(img)

    def height(size):  # both languages share the space; same font size for both
        f = font(FONT_BOLD, size)
        blocks = [wrap(d, story[k], f, w) for k in ("en", "ne")]
        if any(d.textlength(line, font=f) > w for bl in blocks for line in bl):
            return 10 ** 6
        return sum(len(bl) for bl in blocks) * int(size * line_h) + gap

    size = st.get("max_px", HEADLINE_MAX_PX)
    while size > 40 and height(size) > y1 - y0:
        size -= 2
    f, lh = font(FONT_BOLD, size), int(size * line_h)
    blocks = [balanced_wrap(d, story[k], f, w) for k in ("en", "ne")]
    ty = y0 + (y1 - y0 - (sum(len(bl) for bl in blocks) * lh + gap)) // 2
    for i, bl in enumerate(blocks):
        for line in bl:
            lx = x + (w - d.textlength(line, font=f)) // 2
            colour = st["text"] if i == 0 else st.get("text_ne", st["text"])  # Nepali in the accent colour
            d.text((lx, ty), line, font=f, fill=colour, stroke_width=st.get("stroke_w", TEXT_STROKE),
                   stroke_fill=st["stroke"])
            ty += lh
        if i == 0:  # small red divider between English and Nepali
            my = ty + gap // 2 - lh * 0.08
            d.line([(627 - 190, my), (627 + 190, my)], fill=(220, 30, 45), width=4)
            ty += gap

    if credit:  # small, semi-transparent photo credit
        layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
        ImageDraw.Draw(layer).text((r - 50, b - 22), f"Photo: {story['source']}", font=font(FONT_BOLD, 17),
                                   fill=st["credit"], anchor="rs")
        img = Image.alpha_composite(img.convert("RGBA"), layer).convert("RGB")
        d = ImageDraw.Draw(img)

    stamp = date_stamp(story.get("post_ts") or time.time())
    sf = font(FONT_BOLD, date_px)
    cx, sw = 627, d.textlength(stamp, font=sf)
    ph_ = int(date_px * 0.75)                    # pill half-height follows the font size
    d.rounded_rectangle([cx - sw / 2 - 24, pill_y - ph_, cx + sw / 2 + 24, pill_y + ph_],
                        radius=ph_, fill=(8, 14, 32), outline=(220, 30, 45), width=2)
    d.text((cx, pill_y), stamp, font=sf, fill=(255, 255, 255), anchor="mm")
    path = OUT / f"{int(time.time()*1000)}_{theme}.jpg"
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


def clean_tag(t):
    """'Prithvi Highway' -> 'PrithviHighway'; keeps letters, digits and Devanagari; max 30 chars."""
    t = "".join(w[:1].upper() + w[1:] for w in re.split(r"[^\w\u0900-\u097F]+", str(t)) if w)
    return t[:30] if len(t) >= 3 and not t.isdigit() else ""


TAG_SKIP = {"Nepal", "Nepali", "News", "The", "A", "An", "In", "On", "At", "Of", "For", "And", "To", "With",
            "After", "Over", "From", "By", "As", "Is", "Are", "Says", "Said", "New", "Its", "His", "Her"}


def topic_tags(s):
    """Hashtags for this story: from the AI (\"h\"), else capitalised names + urgent keywords in the headline."""
    tags = list(s.get("tags") or [])
    if not tags:
        words = re.findall(r"[A-Za-z][A-Za-z'-]*", s["en"])
        names, run = [], []
        for i, w in enumerate(words + ["x"]):          # runs of capitalised words = one name
            if w[0].isupper() and w not in TAG_SKIP and i < len(words):
                run.append(w)
            else:
                if run:
                    names.append("".join(run))
                run = []
        topics = [m for m in BREAKING.findall(s["en"]) if not m.lower().endswith(("ed", "s"))]
        tags = [clean_tag(m) for m in topics] + [clean_tag(n) for n in names]
    out, low = [], {t.lower().lstrip("#") for t in (HASHTAGS_EN + " " + HASHTAGS_NE).split()} | {"nepal", "news"}
    for t in tags:
        if t and t.lower() not in low:
            out.append("#" + t); low.add(t.lower())
    return out[:4]


def captions(s):
    """Facebook: both languages. Instagram: English only. Story hashtags first, then the brand tags."""
    # Instagram counts at most 5 hashtags per post (Dec 2025 rule): story tags first, then the brand tags
    brand = HASHTAGS_EN.split()
    story = topic_tags(s)[:max(0, MAX_HASHTAGS - len(brand))]
    tags = " ".join(story + brand)
    fb = (f"{s['en']}\n{s['ne']}\n\n"
          f"Source / स्रोत: {s['source']}\n"
          f"Read more / पूरा समाचार: {s['link']}\n\n{tags}")
    # Instagram caption: English only (the image already carries both languages)
    en_story = [t for t in topic_tags(s) if t.isascii()][:max(0, MAX_HASHTAGS - len(brand))]
    ig = (f"{s['en']}\n\n"
          f"Source: {s['source']}\n"
          f"Full story: {s['link']}\n\n{' '.join(en_story + brand)}")
    return fb, ig


def ig_quota():
    """Instagram's own count of API posts in the last rolling 24h (includes deleted posts
    and anything posted outside this bot). None if it can't be read."""
    try:
        j = graph("GET", f"{os.environ['IG_USER_ID']}/content_publishing_limit", fields="quota_usage,config")
        return int(j["data"][0]["quota_usage"])
    except Exception as ex:
        log(f"could not read IG quota: {ex!r}")
        return None


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

    # 0. nothing can be posted for a while (Meta block, or the 24h cap is full)? Then skip the
    #    whole run: no feed fetching, no AI calls. Work resumes 45 min before posting is possible,
    #    so the queue is fresh and translated by then.
    if not DRY:
        def fb24(t):
            return sum(p.get("n_fb", 0) for p in posted if t - 86400 < p["ts"] <= now)
        cap_free = now if not FB_DAILY_CAP else next(
            (now + m * 300 for m in range(0, 24 * 12 + 1) if fb24(now + m * 300) + 1 <= FB_DAILY_CAP), now)
        resume = max(cap_free, state.get("fb_block_until", 0))
        if resume - now > RESUME_LEAD_MIN * 60:
            why = "Meta spam-block cooldown" if resume == state.get("fb_block_until") else \
                  f"24h Facebook cap full ({fb24(now)}/{FB_DAILY_CAP})"
            log(f"paused: {why}. Posting possible from "
                f"{datetime.fromtimestamp(resume, NPT):%d %b %H:%M} NPT; skipping this run "
                f"(no fetch, no AI calls)")
            return

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

    # 3. ONE LLM request for up to LLM_BATCH new items (rest wait for next run).
    #    Batched to save tokens: call only when enough headlines are waiting, one has waited too long,
    #    or something looks urgent. Otherwise they are simply picked up again next run.
    if new and not state.get("pending_since"):
        state["pending_since"] = now
    if not new:
        state["pending_since"] = None
    waited = now - (state.get("pending_since") or now) >= LLM_MAX_WAIT_MIN * 60
    critical = [n for n in new if CRITICAL.search(n["title"])]
    mode = "full" if new and (waited or len(new) >= LLM_MIN_BATCH) else "urgent" if critical else None
    if new and not mode:
        log(f"{len(new)} new headlines waiting for a fuller batch")
    if mode == "full":
        state["pending_since"] = None if len(new) <= LLM_BATCH else now
    if mode:
        if mode == "full":
            batch = round_robin(new, LLM_BATCH)
            # same-story context: the last 12h's posts (up to 30) + newest 40 queued, trimmed to 60 chars
            posted_ctx = [p["en"][:60] for p in recent_posted if p["ts"] > now - 12 * 3600][-30:]
            queue_ctx = queue[-40:]
        else:
            # small request: only the critical headlines, checked against the last 3h of posts
            batch = critical[:URGENT_MAX]
            posted_ctx = [p["en"][:60] for p in recent_posted if p["ts"] > now - 3 * 3600][-15:]
            queue_ctx = []
        log(f"LLM {mode} call: {len(batch)} headlines, {len(posted_ctx) + len(queue_ctx)} context")
        existing = posted_ctx + [q["en"][:60] for q in queue_ctx]
        n_posted = len(posted_ctx)
        try:
            # small urgent calls go to Gemini first, full batches to Groq first
            done = translate(batch, existing, prefer_gemini=(mode == "urgent"))
        except Exception as ex:
            log(f"{ex}; these {len(batch)} items will retry next run")
            state["pending_since"] = now - LLM_MAX_WAIT_MIN * 60  # retry on the very next run
            done, batch = [], []
        for b in batch:
            seen[b["link"]] = now
        for i, b in enumerate(done):
            d, target = b.pop("dup", None), None
            if isinstance(d, str) and d.startswith("E") and d[1:].isdigit():
                k = int(d[1:])
                target = queue_ctx[k - n_posted] if n_posted <= k < len(existing) else "posted"
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
        imp = q.get("imp")
        if imp is None:  # no AI score: urgent keyword decides
            return fresh and bool(BREAKING.search(q["en"]))
        # AI score 5 is always breaking; 4 needs an urgent keyword too
        return fresh and (imp >= 5 or (imp >= 4 and bool(BREAKING.search(q["en"]))))

    def impact(q):
        return q.get("imp") or 3

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
    fb_budget = (FB_DAILY_CAP - FB_BREAKING_RESERVE) * frac + 1   # posts allowed so far (+1 story slack)
    ig_budget = (IG_DAILY_CAP - IG_BREAKING_RESERVE) * frac + 1
    last_normal = max((p["ts"] for p in posted if p.get("n_fb") and not p.get("brk")), default=0)
    gap_ok = time.time() - last_normal >= (NORMAL_GAP_MIN - 1) * 60  # -1 min: runs drift by a few seconds
    normal_ok = active and gap_ok and (not FB_DAILY_CAP or (
        fb_today + 1 <= fb_budget and fb_24 + 1 <= FB_DAILY_CAP - FB_BREAKING_RESERVE))
    ig_normal_ok = ig_today + 1 <= ig_budget and ig_24 + 1 <= IG_DAILY_CAP - IG_BREAKING_RESERVE
    wait = max(0, (last_normal + NORMAL_GAP_MIN * 60 - time.time()) / 60)
    log(f"next regular story in {wait:.0f} min | "
        f"impact in queue: " + ", ".join(f"{k}:{sum(1 for q in queue if impact(q) == k)}" for k in (5, 4, 3, 2, 1)))
    log(f"{'active' if active else 'quiet hours'} | today FB {fb_today}/{f'{fb_budget:.0f}' if FB_DAILY_CAP else 'no cap'}, "
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
            q["_breaking"] = is_breaking(q)
            log(f"[PREVIEW] {q['source']}{' [BREAKING]' if q['_breaking'] else ''}: photo {'found' if q['_photo'] is not None else 'NOT found'} | {q['en']}")
            for theme in ("dark", "white"):
                log(f"   {theme}: {render(q, theme)}")
        return

    page_links = set() if DRY else recent_page_links()
    q = None if DRY else ig_quota()
    if q is not None:
        log(f"IG quota from Meta: {q}/100 used in last 24h (bot's own count {ig_24})")
        ig_24 = max(ig_24, q)
        ig_normal_ok = ig_normal_ok and ig_24 + 1 <= IG_DAILY_CAP - IG_BREAKING_RESERVE
    n_breaking = n_normal = 0
    blocks = [b for b in state.get("fb_blocks", []) if b > now - 48 * 3600]
    block_until = state.get("fb_block_until", 0)
    if not DRY and time.time() < block_until:
        left = (block_until - time.time()) / 3600
        log(f"Meta spam block cooldown: no posting for {left:.1f}h more (news is still collected)")
        save(state, seen, queue, posted)
        return
    fb_blocked = False
    while queue and not fb_blocked and n_breaking + n_normal < MAX_STORIES_PER_RUN and (not FB_DAILY_CAP or fb_24 + 1 <= FB_DAILY_CAP):
        br = [q for q in queue if is_breaking(q)]
        if (br and (active or BREAKING_24H) and n_breaking < BREAKING_PER_RUN
                and brk_hour + n_breaking < BREAKING_PER_HOUR):
            pool, breaking = br, True
        elif normal_ok and n_normal < STORIES_PER_RUN and any(impact(q) >= NORMAL_MIN_IMPACT for q in queue):
            pool, breaking = [q for q in queue if impact(q) >= NORMAL_MIN_IMPACT], False
        else:
            break
        # most impactful first, then most-covered, then the outlet used least recently, then trusted, then newest
        s = min(pool, key=lambda q: (-impact(q), -q["hits"], recent_src.count(q["source"]), -q["weight"], -q["ts"]))
        queue.remove(s)
        if breaking:
            n_breaking += 1
        else:
            n_normal += 1
        recent_src.append(s["source"])
        # last check right before posting: same story already posted in the last 12h?
        twin = next((p for p in posted if p["ts"] > now - 12 * 3600 and p.get("n_fb")
                     and similar(s["en"], p["en"])), None)
        if twin:
            log(f"same story already posted ({twin['en'][:60]}), skipping: {s['en']}")
            if breaking:
                n_breaking -= 1
            else:
                n_normal -= 1
            continue
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
        s["_breaking"] = breaking
        use_ig = breaking or ig_normal_ok
        if use_ig:
            ig_today += 1
            ig_normal_ok = ig_today + 1 <= ig_budget and ig_24 + 2 <= IG_DAILY_CAP - IG_BREAKING_RESERVE
        # dark and white templates take turns (THEME = "alternate"), or a fixed one
        theme = THEME if THEME in STYLES else ("dark", "white")[sum(1 for p in posted if p.get("n_fb")) % 2]
        img = render(s, theme)
        fb_text, ig_text = captions(s)
        if DRY:
            log(f"[DRY] {img}\n--- caption ---\n{fb_text}\n")
        else:
            try:
                pid, url = post_facebook(img, fb_text)
                rec["n_fb"] += 1; fb_24 += 1
                log(f"FB ok {pid} ({theme}){' [BREAKING]' if breaking else ''} impact {s.get('imp')}")
                if use_ig and ig_24 + 1 <= IG_DAILY_CAP - (0 if breaking else IG_BREAKING_RESERVE):
                    log(f"IG ok {post_instagram(url, ig_text)}")
                    rec["n_ig"] += 1; ig_24 += 1
            except Exception as ex:
                log("POST FAIL:\n" + traceback.format_exc())
                if "'code': 368" in str(ex):  # Meta rate/spam block: stop and back off, don't keep hammering
                    hours = BLOCK_COOLDOWN_H * 2 ** len(blocks)
                    blocks.append(time.time())
                    state["fb_blocks"] = blocks
                    state["fb_block_until"] = time.time() + hours * 3600
                    log(f"Meta spam block (368): pausing all posting for {hours}h")
                    fb_blocked = True
                    if rec["n_fb"] == 0 and rec in posted:  # nothing went out: keep the story for later
                        posted.remove(rec)
                        queue.append(s)
            save(state, seen, queue, posted)
        s.pop("_photo", None)
        s.pop("_breaking", None)
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
