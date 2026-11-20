"""
MovieBox catalog scraper -> split <23MB JSON chunks for an Android streaming app.

Reverse-engineered from github.com/mesamirh/MovieBox-TUI (providers/moviebox).
Replicates: visitor login, HMAC-MD5 request signing, homepage tabs, search
pagination, details, play-info (signed DASH manifests), resources.

Run:
    pip install requests
    python moviebox_TUI_scraper.py                 # full run
    python moviebox_TUI_scraper.py --max-titles 25 # quick test run
    python moviebox_TUI_scraper.py --max-titles 25 --fresh   # ignore saved progress

Output (saved inside repo's output/ folder):
    output/index.json                (manifest with SHA-256 version_hash)
    output/catalog_part_1.json       (split chunks capped under 23 MB)
    output/moviebox_progress.jsonl   (progress log, resume-safe)
"""

import argparse
import base64
import hashlib
import hmac
import json
import os
import random
import re
import time

import requests

# ---------------------------------------------------------------- config ----

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
OUT_DIR = os.path.join(BASE_DIR, "output")
INDEX_FILE = os.path.join(OUT_DIR, "index.json")
PROGRESS_FILE = os.path.join(OUT_DIR, "moviebox_progress.jsonl")

# 22.5 MB safe ceiling so every chunk stays strictly under 23 MB
MAX_CHUNK_BYTES = 22 * 1024 * 1024 + 512 * 1024

HOST_POOL = [
    "https://api6.aoneroom.com",
    "https://api5.aoneroom.com",
    "https://api4.aoneroom.com",
    "https://api4sg.aoneroom.com",
    "https://api3.aoneroom.com",
    "https://api6sg.aoneroom.com",
    "https://api.inmoviebox.com",
]

RETRY_STATUS = {403, 406, 407, 429, 500, 502, 503, 504}

# HMAC-MD5 key lifted from providers/moviebox/crypto.rs
SECRET_KEY = bytes([
    0xEF, 0xA8, 0x91, 0x97, 0x4E, 0xEC, 0xD3, 0x14,
    0x8D, 0xF6, 0x3A, 0xA6, 0x11, 0x60, 0x2D, 0xEF,
    0xD1, 0x01, 0x25, 0x9B, 0xA5, 0x21, 0x02, 0x2C,
    0x57, 0xAE, 0x05, 0x66, 0xBD, 0x8E,
])

STOCK_CERT_SHA256 = "03d4b741632d136bc23e2de4c6adcdb7712f1980b619c183221801730bbd0410"
BUILD_TAG_SALT = "oneroom"

STREAM_REFERER = "https://sportslive.wine"

SIGNATURE_BODY_MAX_BYTES = 102_400

# Tab ids used by the app's browse page. Extra ids are harmless.
TAB_IDS = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]

# Search seeds - the API needs a keyword, so we sweep the common ones.
SEARCH_SEEDS = [
    "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
    "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
    "0", "1", "2", "3", "4", "5", "6", "7", "8", "9",
    "the", "love", "war", "man", "dark", "night", "star", "india",
    "hindi", "tamil", "telugu", "korean", "anime", "season",
]

PER_PAGE = 15
MAX_SEARCH_PAGES = 40          # hard cap per seed
REQUEST_DELAY = 0.35           # polite spacing, keeps 429s down
MAX_HOMEPAGE_PAGES = 10


# ------------------------------------------------------------- signing -----

def md5_hex(data: bytes) -> str:
    return hashlib.md5(data).hexdigest()


def client_token(ts_ms: int) -> str:
    ts_str = str(ts_ms)
    return f"{ts_str},{md5_hex(ts_str[::-1].encode())}"


def build_tag(ts_ms: int, rand_part: int) -> str:
    stamp = f"{ts_ms // 1000}{ts_ms % 1000:03d}000{rand_part}"
    digest = md5_hex(f"{STOCK_CERT_SHA256}{BUILD_TAG_SALT}{stamp}".encode())
    return f"{stamp}.{digest}"


def canonical_string(method, accept, content_type, url, body, ts_ms) -> str:
    from urllib.parse import urlparse, parse_qsl

    parsed = urlparse(url)
    path = parsed.path or "/"
    pairs = sorted(parse_qsl(parsed.query, keep_blank_values=True))
    canonical_url = f"{path}?{'&'.join(f'{k}={v}' for k, v in pairs)}" if pairs else path

    if body is not None:
        raw = body.encode()
        truncated = raw[:SIGNATURE_BODY_MAX_BYTES]
        body_hash = md5_hex(truncated)
        body_len = str(len(raw))
    else:
        body_hash = ""
        body_len = ""

    return "\n".join([
        method.upper(),
        accept or "",
        content_type or "",
        body_len,
        str(ts_ms),
        body_hash,
        canonical_url,
    ])


def tr_signature(method, accept, content_type, url, body, ts_ms) -> str:
    canon = canonical_string(method, accept, content_type, url, body, ts_ms)
    sig = hmac.new(SECRET_KEY, canon.encode(), hashlib.md5).digest()
    return f"{ts_ms}|2|{base64.b64encode(sig).decode()}"


def random_hex(n: int) -> str:
    return "".join(random.choice("0123456789abcdef") for _ in range(n))


def random_spoofed_ip() -> str:
    prefix = random.choice([
        "103.241", "49.36", "117.195", "106.198", "122.162",
        "157.32", "182.70", "103.58", "27.60", "59.90",
    ])
    return f"{prefix}.{random.randint(1, 253)}.{random.randint(1, 253)}"


ANDROID_VERSIONS = [
    ("9", "PQ3A.190605.03081104"),
    ("10", "QP1A.191005.007.A3"),
    ("11", "RP1A.200720.011"),
    ("12", "S1B.220414.015"),
    ("13", "TQ2A.230405.003"),
]
REDMI_DEVICES = [
    "23078RKD5C", "2201117TY", "2201117TG", "22101316G",
    "21121210G", "M2012K11AG", "M2007J20CG",
]
VERSION_CODES = [50020117, 50020118, 50020119, 50020120, 50020121]


def generate_identity():
    android, build_id = random.choice(ANDROID_VERSIONS)
    device = random.choice(REDMI_DEVICES)
    version_code = random.choice(VERSION_CODES)
    network = random.choice(["NETWORK_WIFI", "NETWORK_MOBILE"])
    tz = random.choice(["Asia/Kolkata", "Asia/Shanghai", "Asia/Tokyo",
                        "America/New_York", "Europe/London"])
    gaid = "-".join([random_hex(8), random_hex(4), random_hex(4),
                     random_hex(4), random_hex(12)])
    device_id = random_hex(32)

    ua = (f"com.community.oneroom/{version_code} (Linux; U; Android {android}; "
          f"en_US; {device}; Build/{build_id}; Cronet/135.0.7012.3)")

    client_info = {
        "package_name": "com.community.oneroom",
        "version_name": "4.0.01.0813.03",
        "version_code": version_code,
        "os": "android",
        "os_version": android,
        "install_ch": "ps",
        "device_id": device_id,
        "install_store": "ps",
        "gaid": gaid,
        "brand": "Redmi",
        "model": device,
        "system_language": "en",
        "net": network,
        "region": "US",
        "timezone": tz,
        "sp_code": "40401",
        "X-Play-Mode": "2",
    }
    return ua, client_info


# -------------------------------------------------------------- client -----

class MovieBox:
    def __init__(self):
        self.ua, self.client_info = generate_identity()
        self.ip = random_spoofed_ip()
        self.token = None
        self.base_idx = 0
        self.sess = requests.Session()

    # -- low level ---------------------------------------------------------

    def _signed_headers(self, method, url, body, token=None):
        ts = int(time.time() * 1000)
        accept = "application/json"
        ctype = "application/json"

        tag = build_tag(ts, random.randrange(0, 1000))
        info = dict(self.client_info)
        info["X-Client-Build"] = tag

        headers = {
            "User-Agent": self.ua,
            "Accept": accept,
            "Content-Type": ctype,
            "Connection": "keep-alive",
            "x-client-token": client_token(ts),
            "x-tr-signature": tr_signature(method, accept, ctype, url, body, ts),
            "x-client-build": tag,
            "x-client-info": json.dumps(info, separators=(",", ":")),
            "x-client-status": "0",
            "x-forwarded-for": self.ip,
        }
        if token:
            headers["Authorization"] = f"Bearer {token}"
        return headers

    def _raw_request(self, method, path, body=None, token=None):
        """Try every host until one answers. Returns parsed JSON or None."""
        start = self.base_idx
        backoff = 0.05

        for i in range(len(HOST_POOL)):
            idx = (start + i) % len(HOST_POOL)
            base = HOST_POOL[idx]
            url = base + path

            try:
                headers = self._signed_headers(method, url, body, token)
                resp = self.sess.request(
                    method, url, headers=headers,
                    data=body.encode() if body else None, timeout=15,
                )
            except requests.RequestException as exc:
                log(f"  host {idx} net error: {exc}")
                self.base_idx = (idx + 1) % len(HOST_POOL)
                continue

            if resp.status_code in RETRY_STATUS:
                self.base_idx = (idx + 1) % len(HOST_POOL)
                if resp.status_code == 429:
                    ra = resp.headers.get("Retry-After", "0")
                    try:
                        backoff = min(float(ra), 3.0)
                    except ValueError:
                        backoff = 0.4
                time.sleep(backoff)
                continue

            if resp.status_code >= 400:
                log(f"  host {idx} status {resp.status_code}")
                continue

            self.base_idx = idx
            try:
                payload = resp.json()
            except ValueError:
                log(f"  host {idx} bad json")
                continue

            return payload.get("data", payload) if isinstance(payload, dict) else payload

        return None

    def _request(self, method, path, body=None, _retry=True):
        if not self.token:
            if not self.login():
                return None
        result = self._raw_request(method, path, body, self.token)
        if result is None and _retry:
            log("  session might be dead, re-logging in")
            self.token = None
            if self.login():
                return self._raw_request(method, path, body, self.token)
        return result

    def get(self, path):
        return self._request("GET", path)

    def post(self, path, payload):
        return self._request("POST", path, json.dumps(payload, separators=(",", ":")))

    # -- api ---------------------------------------------------------------

    def login(self):
        for attempt in range(3):
            val = self._raw_request(
                "POST", "/wefeed-mobile-bff/user-api/visitor-login", "{}", None
            )
            if isinstance(val, dict) and val.get("token"):
                self.token = val["token"]
                log("  logged in as visitor")
                return True
            log(f"  login attempt {attempt + 1} failed")
            time.sleep(1.5)
        return False

    def homepage(self, tab_id, page=1):
        return self.get(f"/wefeed-mobile-bff/tab-operating?page={page}&tabId={tab_id}&version=")

    def search(self, keyword, page=1):
        return self.post("/wefeed-mobile-bff/subject-api/search/v2", {
            "keyword": keyword,
            "page": page,
            "perPage": PER_PAGE,
            "subjectType": 0,
        })

    def details(self, subject_id):
        data = self.get(f"/wefeed-mobile-bff/subject-api/get?subjectId={subject_id}")
        if isinstance(data, dict):
            stype = data.get("subjectType") or data.get("stype") or 1
            if int(stype) == 2:
                seasons = self.get(
                    f"/wefeed-mobile-bff/subject-api/season-info?subjectId={subject_id}"
                )
                if seasons:
                    data["seasons"] = seasons
        return data

    def play_info(self, subject_id, season=0, episode=0):
        if season == 0 and episode == 0:
            path = f"/wefeed-mobile-bff/subject-api/play-info/v2?subjectId={subject_id}"
        else:
            path = (f"/wefeed-mobile-bff/subject-api/play-info/v2"
                    f"?subjectId={subject_id}&se={season}&ep={episode}")
        return self.get(path)

    def resources(self, subject_id, season=0, episode=0, page=1, per_page=20):
        if season == 0 and episode == 0:
            path = (f"/wefeed-mobile-bff/subject-api/resource"
                    f"?subjectId={subject_id}&page={page}&perPage={per_page}")
        else:
            path = (f"/wefeed-mobile-bff/subject-api/resource"
                    f"?subjectId={subject_id}&se={season}&ep={episode}"
                    f"&page={page}&perPage={per_page}")
        return self.get(path)


# ------------------------------------------------------------ helpers ------

def log(msg):
    print(msg, flush=True)


NOTICE_MARKERS = [
    "1c7de0bd3393702d9191801f15f88f8d",
    "9a0461bc39da389663bf3dbb17091d3f",
    "b164fbfb4347792950bdfbfb563d39d9",
    "/notice.mp4",
]


def is_notice_url(url: str) -> bool:
    if not url:
        return True
    low = url.lower()
    if any(m in low for m in NOTICE_MARKERS):
        return True
    if "macdn.aoneroom.com" in low and "/other/" in low:
        return True
    return False


def b64_decode_loose(s: str):
    s = s.strip()
    s = s.replace("-", "+").replace("_", "/").replace("~", "/")
    pad = (4 - len(s) % 4) % 4
    if pad:
        s += "=" * pad
    try:
        return base64.b64decode(s)
    except Exception:
        return None


def to_dash_mpd(url: str):
    base = url.rstrip("*").rstrip("/")
    if base.startswith(("http://", "https://")) and "/dash/" in base:
        return base + "/index.mpd"
    return None


def manifest_from_cookie(cookie: str):
    """Pull the signed DASH manifest URL out of a signCookie."""
    if not cookie:
        return None
    for part in cookie.split(";"):
        part = part.strip()
        if not part:
            continue

        if "urlprefix=" in part:
            idx = part.find("urlprefix=")
            chunk = part[idx + len("urlprefix="):]
            token = chunk.split(":")[0].strip()
            decoded = b64_decode_loose(token)
            if decoded:
                try:
                    mpd = to_dash_mpd(decoded.decode("utf-8"))
                    if mpd:
                        return mpd
                except UnicodeDecodeError:
                    pass
            if chunk.startswith(("http://", "https://")):
                mpd = to_dash_mpd(chunk.split(":sign")[0])
                if mpd:
                    return mpd

        if part.startswith("CloudFront-Policy="):
            raw = part[len("CloudFront-Policy="):].strip()
            decoded = b64_decode_loose(raw)
            if not decoded:
                continue
            try:
                policy = json.loads(decoded)
            except ValueError:
                continue
            stmts = policy.get("Statement") or []
            if stmts:
                res = stmts[0].get("Resource")
                if isinstance(res, str):
                    mpd = to_dash_mpd(res)
                    if mpd:
                        return mpd
    return None


def clean_cookie(cookie: str) -> str:
    parts = [p.strip() for p in cookie.split(";") if p.strip()]
    return "; ".join(parts)


def extract_year(raw):
    if not raw or not isinstance(raw, str):
        return None
    for i in range(len(raw) - 3):
        chunk = raw[i:i + 4]
        if chunk.isdigit() and 1900 <= int(chunk) <= 2099:
            return chunk
    return None


def quality_label(resolution):
    if resolution is None:
        return None
    s = str(resolution).strip()
    if s.isdigit():
        return f"{s}p"
    return s or None


def detect_format(url: str):
    if not url:
        return None
    low = url.lower()
    if ".m3u8" in low:
        return "m3u8"
    if "/dash/" in low or ".mpd" in low:
        return "mpd"
    if ".mp4" in low:
        return "mp4"
    return "unknown"


def add_stream(bucket, item, source_link_hint=None):
    """Add one resource item to a stream bucket."""
    if not isinstance(item, dict):
        return
    link = item.get("resourceLink") or item.get("url") or item.get("downloadUrl")
    if link and is_notice_url(link):
        link = None

    resolution = item.get("resolution")
    if resolution is None and source_link_hint:
        m = re.search(r"(?<!\d)(\d{3,4})[pP]", str(source_link_hint))
        if m:
            resolution = m.group(1)

    entry = {
        "quality": quality_label(resolution),
        "url": link,
        "format": detect_format(link) if link else None,
        "codec": item.get("codecName") or item.get("codec"),
        "size": item.get("size"),
        "season": item.get("se"),
        "episode": item.get("ep"),
    }
    if not link:
        entry["note"] = "no direct url in resource listing"
    bucket.append(entry)


def subjects_from_search(payload):
    if not isinstance(payload, dict):
        return []
    results = payload.get("results")
    if isinstance(results, list) and results:
        subjects = results[0].get("subjects")
        if isinstance(subjects, list):
            return subjects
    for key in ("list", "subjects", "items"):
        val = payload.get(key)
        if isinstance(val, list):
            return val
    return []


def subjects_from_homepage(payload):
    if not isinstance(payload, dict):
        return []
    out = []
    groups = payload.get("items")
    if not isinstance(groups, list):
        groups = payload if isinstance(payload, list) else []
    for group in groups:
        if not isinstance(group, dict):
            continue
        for subj in (group.get("subjects") or []):
            if isinstance(subj, dict):
                out.append(subj)
        banner = (group.get("banner") or {}).get("banners") or []
        for b in banner:
            if isinstance(b, dict) and isinstance(b.get("subject"), dict):
                out.append(b["subject"])
        custom = (group.get("customData") or {}).get("items") or []
        for c in custom:
            if isinstance(c, dict) and isinstance(c.get("subject"), dict):
                out.append(c["subject"])
    return out


def subject_to_entry(subject, moviebox, with_streams=True):
    """Turn an API subject into one catalog entry."""
    sid = subject.get("subjectId") or subject.get("id")
    if sid is None:
        return None
    sid = str(sid)

    stype = subject.get("subjectType") or subject.get("stype") or 1
    is_series = int(stype) == 2

    cover = None
    if isinstance(subject.get("cover"), dict):
        cover = subject["cover"].get("url")
    cover = cover or subject.get("coverUrl") or subject.get("poster") or subject.get("pic")

    entry = {
        "id": sid,
        "title": subject.get("title") or subject.get("name") or "Unknown",
        "type": "series" if is_series else "movie",
        "year": extract_year(subject.get("releaseDate") or subject.get("year")
                             or subject.get("releaseInfo")),
        "poster": cover,
        "description": subject.get("description") or subject.get("intro"),
        "rating": subject.get("imdbRatingValue") or subject.get("rating"),
        "director": subject.get("director"),
        "cast": subject.get("stars"),
        "genres": subject.get("genre") if isinstance(subject.get("genre"), list) else None,
        "duration": subject.get("duration"),
        "season_count": subject.get("season"),
        "streams": [],
        "episodes": [],
        "dubs": [],
    }

    if not with_streams:
        return entry

    details = moviebox.details(sid)
    if isinstance(details, dict):
        for key in ("description", "director", "stars", "duration"):
            if not entry.get(key) and details.get(key):
                entry[key] = details[key]
        if not entry.get("rating") and details.get("imdbRatingValue"):
            entry["rating"] = details["imdbRatingValue"]
        if isinstance(details.get("genre"), list) and not entry.get("genres"):
            entry["genres"] = details["genre"]

        dubs = details.get("dubs")
        if isinstance(dubs, list):
            entry["dubs"] = [
                {
                    "subject_id": str(d.get("subjectId") or d.get("id") or ""),
                    "language": d.get("lanName") or d.get("language") or d.get("lang"),
                    "label": d.get("title") or d.get("name") or d.get("lanName"),
                }
                for d in dubs if isinstance(d, dict)
            ]

        # direct files from resourceDetectors
        for det in details.get("resourceDetectors") or []:
            if not isinstance(det, dict):
                continue
            rlist = det.get("resolutionList") or []
            if rlist:
                for item in rlist:
                    add_stream(entry["streams"], item)
            else:
                add_stream(entry["streams"], {
                    "resourceLink": det.get("downloadUrl"),
                    "resourceId": det.get("resourceId"),
                    "size": det.get("firstSize"),
                    "codecName": det.get("codecName"),
                    "se": 0,
                    "ep": 0,
                }, source_link_hint=det.get("resourceLink"))

        # season / episode skeleton
        season_payload = details.get("seasons")
        seasons_list = None
        if isinstance(season_payload, dict):
            seasons_list = season_payload.get("seasons")
        elif isinstance(season_payload, list):
            seasons_list = season_payload
        if isinstance(seasons_list, list):
            for s in seasons_list:
                if not isinstance(s, dict):
                    continue
                se = int(s.get("se") or 1)
                numbers = []
                eps = s.get("episodeNumbers")
                if isinstance(eps, list) and eps:
                    for e in eps:
                        try:
                            numbers.append(int(e))
                        except (TypeError, ValueError):
                            pass
                else:
                    max_ep = int(s.get("maxEp") or 0)
                    numbers = list(range(1, max_ep + 1))
                for number in numbers:
                    entry["episodes"].append({
                        "season": se,
                        "episode": number,
                        "streams": [],
                    })

    def harvest(payload, season=0, episode=0):
        """Collect signed streams from a play-info payload."""
        if not isinstance(payload, dict):
            return
        data = payload.get("data", payload)
        for st in data.get("streams") or []:
            if not isinstance(st, dict):
                continue
            cookie = st.get("signCookie") or ""
            playable = manifest_from_cookie(cookie)
            if not playable:
                raw_url = st.get("url") or ""
                playable = None if is_notice_url(raw_url) else (raw_url or None)
            if not playable:
                continue

            hdrs = {"Referer": STREAM_REFERER, "User-Agent": moviebox.ua}
            if cookie:
                hdrs["Cookie"] = clean_cookie(cookie)

            res_str = st.get("resolutions") or data.get("displayResolutions") or "1080"
            resolutions = []
            for r in str(res_str).split(","):
                r = r.strip()
                if r.isdigit():
                    resolutions.append(int(r))
            if not resolutions:
                resolutions = [1080]
            resolutions = sorted(set(resolutions), reverse=True)

            for res in resolutions:
                stream_obj = {
                    "quality": f"{res}p",
                    "url": playable,
                    "format": detect_format(playable),
                    "codec": st.get("codecName") or st.get("codec"),
                    "size": st.get("size"),
                    "headers": hdrs,
                    "season": season or None,
                    "episode": episode or None,
                }
                if season and episode:
                    for ep in entry["episodes"]:
                        if ep["season"] == season and ep["episode"] == episode:
                            ep["streams"].append(dict(stream_obj))
                            break
                else:
                    entry["streams"].append(stream_obj)

    if is_series and entry["episodes"]:
        for ep in entry["episodes"]:
            payload = moviebox.play_info(sid, ep["season"], ep["episode"])
            time.sleep(REQUEST_DELAY)
            harvest(payload, ep["season"], ep["episode"])
    else:
        payload = moviebox.play_info(sid)
        time.sleep(REQUEST_DELAY)
        harvest(payload)

    # resource listing fallback (older / alternate releases)
    res_payload = moviebox.resources(sid)
    time.sleep(REQUEST_DELAY)
    if isinstance(res_payload, dict):
        for item in res_payload.get("list") or []:
            add_stream(entry["streams"], item)

    seen = set()
    uniq = []
    for s in entry["streams"]:
        key = s.get("url")
        if not key or key in seen:
            continue
        seen.add(key)
        uniq.append(s)
    entry["streams"] = uniq

    return entry


# -------------------------------------------------------- progress io ------

def load_progress():
    done = {}
    if not os.path.exists(PROGRESS_FILE):
        return done
    with open(PROGRESS_FILE, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except ValueError:
                continue
            sid = rec.get("id")
            if sid:
                done[str(sid)] = rec
    return done


def append_progress(entry):
    os.makedirs(OUT_DIR, exist_ok=True)
    with open(PROGRESS_FILE, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, ensure_ascii=False) + "\n")


# ---------------------------------------------------------------- main -----

def write_catalog(done):
    """Split collected movies & series into <23MB JSON chunks + index.json inside output/."""
    os.makedirs(OUT_DIR, exist_ok=True)

    movies, series = [], []
    for entry in done.values():
        if entry.get("type") == "series":
            series.append(entry)
        else:
            movies.append(entry)

    all_items = movies + series

    # Remove old split chunk files before writing fresh ones
    for fname in os.listdir(OUT_DIR):
        if fname.startswith("catalog_part_") and fname.endswith(".json"):
            os.remove(os.path.join(OUT_DIR, fname))

    part_num = 1
    current_chunk = []
    current_bytes = 2  # '[' and ']'
    generated_files = []
    hasher = hashlib.sha256()

    for item in all_items:
        serialized = json.dumps(item, ensure_ascii=False, separators=(",", ":"))
        encoded = serialized.encode("utf-8")
        hasher.update(encoded)
        item_len = len(encoded) + 1  # +1 for comma separator

        if current_chunk and (current_bytes + item_len > MAX_CHUNK_BYTES):
            filename = f"catalog_part_{part_num}.json"
            tmp_path = os.path.join(OUT_DIR, filename + ".tmp")
            final_path = os.path.join(OUT_DIR, filename)
            with open(tmp_path, "w", encoding="utf-8") as fh:
                json.dump(current_chunk, fh, ensure_ascii=False, separators=(",", ":"))
            os.replace(tmp_path, final_path)
            generated_files.append(filename)

            part_num += 1
            current_chunk = []
            current_bytes = 2

        current_bytes += item_len
        current_chunk.append(item)

    if current_chunk:
        filename = f"catalog_part_{part_num}.json"
        tmp_path = os.path.join(OUT_DIR, filename + ".tmp")
        final_path = os.path.join(OUT_DIR, filename)
        with open(tmp_path, "w", encoding="utf-8") as fh:
            json.dump(current_chunk, fh, ensure_ascii=False, separators=(",", ":"))
        os.replace(tmp_path, final_path)
        generated_files.append(filename)

    manifest = {
        "version_hash": hasher.hexdigest(),
        "updated_at_epoch": int(time.time()),
        "total_items": len(all_items),
        "total_parts": len(generated_files),
        "files": generated_files,
    }
    tmp_index = INDEX_FILE + ".tmp"
    with open(tmp_index, "w", encoding="utf-8") as fh:
        json.dump(manifest, fh, ensure_ascii=False, indent=2)
    os.replace(tmp_index, INDEX_FILE)

    return {
        "movies": len(movies),
        "series": len(series),
        "total": len(all_items),
        "parts": len(generated_files),
    }


def main():
    parser = argparse.ArgumentParser(description="Scrape the MovieBox catalog into <23MB JSON chunks.")
    parser.add_argument("--max-titles", type=int, default=0,
                        help="Stop after N titles (0 = no limit).")
    parser.add_argument("--fresh", action="store_true",
                        help="Ignore saved progress and start over.")
    parser.add_argument("--metadata-only", action="store_true",
                        help="Skip stream lookups (much faster, no playable URLs).")
    parser.add_argument("--seeds", default="",
                        help="Comma-separated search keywords instead of the default sweep.")
    args = parser.parse_args()

    os.makedirs(OUT_DIR, exist_ok=True)
    log(f"output folder -> {OUT_DIR}")

    if args.fresh and os.path.exists(PROGRESS_FILE):
        os.remove(PROGRESS_FILE)
        log("progress cleared (--fresh)")

    done = load_progress()
    log(f"resume: {len(done)} titles already collected")

    seeds = SEARCH_SEEDS
    if args.seeds:
        seeds = [s.strip() for s in args.seeds.split(",") if s.strip()]

    mb = MovieBox()
    if not mb.login():
        log("could not log in - the API may be down or blocking this IP")
        return 1

    limit = args.max_titles if args.max_titles > 0 else None

    # fast path: metadata only, pull ids straight from search, skip stream work
    if args.metadata_only:
        remaining = limit or 10 ** 9
        for seed in seeds:
            if remaining <= 0:
                break
            for page in range(1, MAX_SEARCH_PAGES + 1):
                if remaining <= 0:
                    break
                payload = mb.search(seed, page)
                time.sleep(REQUEST_DELAY)
                subjects = subjects_from_search(payload)
                if not subjects:
                    break
                for s in subjects:
                    if remaining <= 0:
                        break
                    sid = s.get("subjectId") or s.get("id")
                    if sid is None:
                        continue
                    sid = str(sid)
                    if sid in done:
                        continue
                    entry = subject_to_entry(s, mb, with_streams=False)
                    if not entry:
                        continue
                    append_progress(entry)
                    done[sid] = entry
                    remaining -= 1
                    log(f"{entry['title'][:45]} ({entry['type']})")
        counts = write_catalog(done)
        log(f"done: {counts['movies']} movies, {counts['series']} series -> {counts['parts']} chunks in {OUT_DIR}")
        return 0

    # 1. gather subject ids from homepage tabs + search seeds
    candidates = {}

    log("collecting homepage tabs")
    for tab in TAB_IDS:
        for page in range(1, MAX_HOMEPAGE_PAGES + 1):
            payload = mb.homepage(tab, page)
            time.sleep(REQUEST_DELAY)
            subjects = subjects_from_homepage(payload)
            if not subjects:
                break
            added = 0
            for s in subjects:
                sid = s.get("subjectId") or s.get("id")
                if sid is None:
                    continue
                sid = str(sid)
                if sid not in candidates:
                    candidates[sid] = s
                    added += 1
            log(f"  tab {tab} page {page}: +{added}")
            if added == 0:
                break
            if limit and len(candidates) >= limit:
                break
        if limit and len(candidates) >= limit:
            break

    if not (limit and len(candidates) >= limit):
        log("collecting search results")
        for seed in seeds:
            for page in range(1, MAX_SEARCH_PAGES + 1):
                payload = mb.search(seed, page)
                time.sleep(REQUEST_DELAY)
                subjects = subjects_from_search(payload)
                if not subjects:
                    break
                added = 0
                for s in subjects:
                    sid = s.get("subjectId") or s.get("id")
                    if sid is None:
                        continue
                    sid = str(sid)
                    if sid not in candidates:
                        candidates[sid] = s
                        added += 1
                if page % 10 == 0:
                    log(f"  '{seed}' page {page}: total ids {len(candidates)}")
                if added == 0 and page > 1:
                    break
                if limit and len(candidates) >= limit:
                    break
            if limit and len(candidates) >= limit:
                break

    log(f"total unique titles found: {len(candidates)}")

    # 2. pull details + streams for each
    pending = [sid for sid in candidates if sid not in done]
    if limit:
        pending = pending[:limit]
    log(f"to fetch: {len(pending)}")

    for i, sid in enumerate(pending, 1):
        subject = candidates[sid]
        try:
            entry = subject_to_entry(subject, mb, with_streams=True)
        except Exception as exc:
            log(f"[{i}/{len(pending)}] {sid} FAILED: {exc}")
            entry = None

        if entry:
            append_progress(entry)
            done[sid] = entry
            log(f"[{i}/{len(pending)}] {entry['title'][:45]} "
                f"({entry['type']}) streams={len(entry['streams'])} "
                f"eps={len(entry['episodes'])}")
        else:
            fallback = subject_to_entry(subject, mb, with_streams=False)
            if fallback:
                fallback["note"] = "details fetch failed"
                append_progress(fallback)
                done[sid] = fallback
                log(f"[{i}/{len(pending)}] {sid} saved metadata only")

        # checkpoint the catalog every 25 titles so a crash leaves a usable file
        if i % 25 == 0:
            counts = write_catalog(done)
            log(f"  checkpoint: {counts['total']} titles written across {counts['parts']} chunks")

        time.sleep(REQUEST_DELAY)

    counts = write_catalog(done)
    log(f"done: {counts['movies']} movies, {counts['series']} series -> {counts['parts']} chunks in {OUT_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
