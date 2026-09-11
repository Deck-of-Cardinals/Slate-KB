from __future__ import annotations

import argparse
import hashlib
import html
import io
import json
import os
import re
import sys
import time
from collections import deque
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit

import requests
from bs4 import BeautifulSoup, NavigableString, Tag
from pypdf import PdfReader


SKIP_EXTENSIONS = {
    ".7z", ".avi", ".bmp", ".css", ".csv", ".doc", ".docx", ".eot", ".exe",
    ".gif", ".ico", ".ics", ".jpeg", ".jpg", ".js", ".json", ".m4a", ".m4v",
    ".mov", ".mp3", ".mp4", ".mpeg", ".mpg", ".odp", ".ods", ".odt", ".ogg",
    ".ogv", ".otf", ".png", ".ppt", ".pptx", ".rar", ".rss", ".svg", ".tar",
    ".tif", ".tiff", ".ttf", ".txt", ".wav", ".webm", ".webp", ".woff", ".woff2",
    ".xls", ".xlsx", ".xml", ".zip"
}

# Keep <form> itself so its labels/help text survive. Interactive controls are removed below.
DROP_TAGS = {
    "script", "style", "noscript", "svg", "canvas", "template",
    "button", "input", "textarea"
}
DROP_SECTIONS = {"nav", "header", "footer"}
KEEP_TAGS = {
    "a", "abbr", "article", "b", "blockquote", "br", "caption", "code", "dd", "del", "details",
    "div", "dl", "dt", "em", "figcaption", "figure", "h1", "h2", "h3", "h4", "h5", "h6",
    "hr", "i", "li", "main", "mark", "ol", "p", "pre", "section", "small", "span", "strong",
    "sub", "summary", "sup", "table", "tbody", "td", "tfoot", "th", "thead", "tr", "u", "ul"
}
TRACKING_QUERY_KEYS = {
    "fbclid", "gclid", "mc_cid", "mc_eid", "utm_campaign", "utm_content", "utm_medium", "utm_source", "utm_term"
}


@dataclass
class Result:
    url: str
    output_path: str | None
    status: str
    title: str | None = None
    fetched_at: str | None = None
    fetch_method: str | None = None
    http_status: int | None = None
    text_chars: int = 0
    note: str | None = None


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def read_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def strip_tracking_query(query: str) -> str:
    pairs = [(k, v) for k, v in parse_qsl(query, keep_blank_values=True) if k.lower() not in TRACKING_QUERY_KEYS]
    return urlencode(pairs, doseq=True)


def normalize_url(url: str, *, keep_query: bool = True) -> str:
    url = url.strip()
    if not url:
        return ""
    parts = urlsplit(url)
    scheme = (parts.scheme or "https").lower()
    netloc = parts.netloc.lower()
    path = re.sub(r"/{2,}", "/", parts.path or "/")
    if path != "/":
        path = path.rstrip("/")
    query = strip_tracking_query(parts.query) if keep_query else ""
    return urlunsplit((scheme, netloc, path, query, ""))


def is_http_url(url: str) -> bool:
    return urlsplit(url).scheme in {"http", "https"}


def path_extension(url: str) -> str:
    name = Path(urlsplit(url).path).name
    if "." not in name:
        return ""
    return Path(name).suffix.lower()


def is_discoverable_html_link(url: str) -> bool:
    ext = path_extension(url)
    return not ext or ext in {".htm", ".html", ".php", ".asp", ".aspx"}


def parse_sources(path: Path) -> tuple[list[str], list[str]]:
    exact: list[str] = []
    wildcards: list[str] = []
    seen_exact: set[str] = set()
    seen_wild: set[str] = set()

    for raw in path.read_text(encoding="utf-8-sig").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue

        if "*" in line:
            if not line.endswith("*") or line.count("*") != 1:
                print(f"WARNING: unsupported wildcard syntax, skipping: {line}", file=sys.stderr)
                continue
            prefix = line[:-1]
            normalized = normalize_url(prefix, keep_query=False)
            if normalized not in seen_wild:
                wildcards.append(prefix)
                seen_wild.add(normalized)
        else:
            normalized = normalize_url(line)
            if normalized and normalized not in seen_exact:
                exact.append(line)
                seen_exact.add(normalized)

    return exact, wildcards


def wildcard_rule(pattern: str) -> tuple[str, str, str]:
    prefix = pattern[:-1]
    p = urlsplit(prefix)
    path_prefix = p.path or "/"
    if not path_prefix.endswith("/"):
        path_prefix += "/"
    seed_path = path_prefix.rstrip("/") or "/"
    seed = urlunsplit((p.scheme, p.netloc, seed_path, "", ""))
    return p.netloc.lower(), path_prefix, seed


def matches_rule(url: str, rule: tuple[str, str, str]) -> bool:
    host, path_prefix, _seed = rule
    p = urlsplit(url)
    path = p.path or "/"
    root = path_prefix.rstrip("/") or "/"
    return p.netloc.lower() == host and (path == root or path.startswith(path_prefix))


def safe_host_folder(host: str) -> str:
    return re.sub(r"[^a-z0-9.-]+", "-", host.lower()).strip("-") or "unknown-host"


def safe_output_path(url: str) -> str:
    p = urlsplit(normalize_url(url))
    host = safe_host_folder(p.netloc)
    raw_parts = [x for x in p.path.split("/") if x]
    parts: list[str] = []

    for item in raw_parts:
        cleaned = re.sub(r"[^A-Za-z0-9._-]+", "-", item).strip("-._")
        parts.append(cleaned[:100] or "page")

    if not parts:
        parts = ["_root"]

    if p.query:
        qhash = hashlib.sha256(p.query.encode("utf-8")).hexdigest()[:10]
        parts.append(f"_query-{qhash}")

    return str(Path("pages", host, *parts, "index.html")).replace(os.sep, "/")


class Fetcher:
    def __init__(self, config: dict):
        self.config = config
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "Deck-of-Cardinals-Slate-KB/1.1 (+https://github.com/Deck-of-Cardinals/Slate-KB)",
            "Accept": "text/html,application/xhtml+xml,application/pdf;q=0.9,*/*;q=0.5",
            "Accept-Language": "en-US,en;q=0.8",
        })
        self._playwright = None
        self._browser = None

    def close(self):
        if self._browser is not None:
            self._browser.close()
        if self._playwright is not None:
            self._playwright.stop()

    def _ensure_browser(self):
        if self._browser is not None:
            return

        from playwright.sync_api import sync_playwright

        self._playwright = sync_playwright().start()
        self._browser = self._playwright.chromium.launch(headless=True)

    def browser_html(self, url: str) -> tuple[str, str, int | None]:
        self._ensure_browser()
        page = self._browser.new_page(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/130 Safari/537.36"
        )
        timeout_ms = int(self.config.get("browser_timeout_seconds", 45) * 1000)

        try:
            response = page.goto(url, wait_until="domcontentloaded", timeout=timeout_ms)

            try:
                page.wait_for_load_state("networkidle", timeout=min(timeout_ms, 12000))
            except Exception:
                pass

            final_url = page.url
            body = page.content()
            status = response.status if response else None
            return final_url, body, status

        finally:
            page.close()

    def get(self, url: str) -> tuple[str, bytes | str, str, int | None, str]:
        timeout = self.config.get("request_timeout_seconds", 35)

        try:
            r = self.session.get(url, timeout=timeout, allow_redirects=True)
            status = r.status_code
            content_type = (r.headers.get("content-type") or "").lower()
            final_url = r.url

            if status < 400 and ("application/pdf" in content_type or final_url.lower().endswith(".pdf")):
                return final_url, r.content, "pdf", status, "requests"

            if status < 400 and ("html" in content_type or not content_type):
                text = r.text
                useful = visible_text_length(text)

                if useful >= int(self.config.get("minimum_useful_text_chars", 350)):
                    return final_url, text, "html", status, "requests"

                if not self.config.get("browser_fallback", True):
                    return final_url, text, "html", status, "requests-sparse"

            if status >= 400 and not self.config.get("browser_fallback", True):
                raise RuntimeError(f"HTTP {status}")

        except requests.RequestException as exc:
            if not self.config.get("browser_fallback", True):
                raise RuntimeError(str(exc)) from exc

        if self.config.get("browser_fallback", True):
            final_url, body, status = self.browser_html(url)
            return final_url, body, "html", status, "playwright"

        raise RuntimeError("No usable response")


def visible_text_length(raw_html: str) -> int:
    soup = BeautifulSoup(raw_html, "html5lib")

    for tag in soup.find_all(list(DROP_TAGS)):
        tag.decompose()

    return len(" ".join(soup.stripped_strings))


def choose_content_root(soup: BeautifulSoup) -> Tag:
    selectors = [
        "main",
        "[role='main']",
        "article",
        "#main-content",
        "#content",
        ".main-content",
        ".content-main",
        ".page-content",
    ]

    for selector in selectors:
        found = soup.select_one(selector)

        if isinstance(found, Tag) and len(" ".join(found.stripped_strings)) >= 150:
            return found

    return soup.body if soup.body else soup


def canonicalize_html(raw_html: str, source_url: str) -> tuple[str, str, list[str], int]:
    soup = BeautifulSoup(raw_html, "html5lib")

    title = ""

    if soup.title and soup.title.string:
        title = " ".join(soup.title.string.split())

    if not title:
        h1 = soup.find("h1")
        title = " ".join(h1.stripped_strings) if h1 else source_url

    root = choose_content_root(soup)

    for tag in root.find_all(list(DROP_TAGS)):
        tag.decompose()

    for tag in root.find_all(list(DROP_SECTIONS)):
        tag.decompose()

    discovered: list[str] = []

    for a in root.find_all("a", href=True):
        absolute = urljoin(source_url, a.get("href", ""))

        if is_http_url(absolute):
            a["href"] = absolute
            discovered.append(absolute)
        else:
            a.attrs.pop("href", None)

    cleaned = BeautifulSoup(str(root), "html5lib")
    body = cleaned.body or cleaned

    for tag in list(body.find_all(True)):
        if tag.name not in KEEP_TAGS:
            tag.unwrap()
            continue

        href = tag.get("href") if tag.name == "a" else None
        tag.attrs = {}

        if href and is_http_url(href):
            tag["href"] = href

    content_html = "\n".join(
        str(child)
        for child in body.contents
        if not isinstance(child, NavigableString) or child.strip()
    )

    text_chars = len(" ".join(body.stripped_strings))

    return title, content_html, discovered, text_chars


def pdf_to_html(data: bytes, source_url: str) -> tuple[str, str, int]:
    reader = PdfReader(io.BytesIO(data))
    blocks: list[str] = []

    for i, page in enumerate(reader.pages, start=1):
        text = (page.extract_text() or "").strip()

        if not text:
            continue

        paras = [x.strip() for x in re.split(r"\n\s*\n", text) if x.strip()]

        page_html = "".join(
            f"<p>{html.escape(p).replace(chr(10), '<br>')}</p>"
            for p in paras
        )

        blocks.append(
            f"<section><h2>Page {i}</h2>{page_html}</section>"
        )

    content = "\n".join(blocks)
    title = Path(urlsplit(source_url).path).name or "PDF document"

    text_chars = len(
        " ".join(
            BeautifulSoup(content, "html.parser").stripped_strings
        )
    )

    return title, content, text_chars


def youtube_video_id(url: str) -> str | None:
    p = urlsplit(url)

    if p.netloc.lower() in {"youtu.be", "www.youtu.be"}:
        return p.path.strip("/") or None

    if "youtube.com" in p.netloc.lower():
        q = dict(parse_qsl(p.query))
        return q.get("v")

    return None


def fetch_youtube_transcript(
    url: str,
    session: requests.Session
) -> tuple[str, str, int] | None:

    video_id = youtube_video_id(url)

    if not video_id:
        return None

    try:
        oembed = session.get(
            "https://www.youtube.com/oembed",
            params={
                "url": f"https://www.youtube.com/watch?v={video_id}",
                "format": "json"
            },
            timeout=20,
        )

        title = (
            oembed.json().get(
                "title",
                f"YouTube video {video_id}"
            )
            if oembed.ok
            else f"YouTube video {video_id}"
        )

    except Exception:
        title = f"YouTube video {video_id}"

    try:
        from youtube_transcript_api import YouTubeTranscriptApi

        api = YouTubeTranscriptApi()
        transcript = api.fetch(video_id)

        lines = [
            getattr(snippet, "text", "").strip()
            for snippet in transcript
            if getattr(snippet, "text", "").strip()
        ]

        if not lines:
            return None

        body = (
            "<section><h2>Transcript</h2>"
            + "".join(
                f"<p>{html.escape(line)}</p>"
                for line in lines
            )
            + "</section>"
        )

        return title, body, len(" ".join(lines))

    except Exception:
        return None


def build_document(
    title: str,
    source_url: str,
    fetched_at: str,
    body_html: str
) -> str:

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<style>
body{{font-family:Arial,Helvetica,sans-serif;max-width:980px;margin:2rem auto;padding:0 1rem;line-height:1.55;color:#171717}}
a{{color:#0645ad}}
table{{border-collapse:collapse;width:100%}}
th,td{{border:1px solid #bbb;padding:.4rem;vertical-align:top}}
.source-meta{{font-size:.82rem;color:#555;border-bottom:1px solid #ddd;padding-bottom:1rem;margin-bottom:1.5rem}}
</style>
</head>
<body>
<div class="source-meta">
<strong>Source:</strong>
<a href="{html.escape(source_url, quote=True)}">{html.escape(source_url)}</a>
<br>
<strong>Mirror refreshed:</strong> {html.escape(fetched_at)}
</div>
{body_html}
</body>
</html>
"""


def rewrite_links(
    document: str,
    current_output: str,
    output_map: dict[str, str],
    keep_source_links: bool
) -> str:

    soup = BeautifulSoup(document, "html.parser")
    current_dir = Path(current_output).parent

    for a in soup.find_all("a", href=True):

        if a.find_parent(class_="source-meta") is not None:
            a["rel"] = "nofollow"
            continue

        href = a["href"]
        key = normalize_url(href)
        target = output_map.get(key)

        if target:
            rel = os.path.relpath(
                target,
                start=current_dir
            ).replace(os.sep, "/")

            a["href"] = rel

        elif not keep_source_links:
            a.unwrap()

        else:
            a["rel"] = "nofollow"

    return str(soup)


def load_existing_manifest(output_dir: Path) -> dict:
    path = output_dir / "_status" / "manifest.json"

    if not path.exists():
        return {}

    try:
        return json.loads(
            path.read_text(encoding="utf-8")
        )
    except Exception:
        return {}


def make_index(
    results: list[Result],
    generated_at: str,
    title: str
) -> str:

    rows = []

    for r in sorted(
        results,
        key=lambda x: x.url.lower()
    ):

        link = (
            f'<a href="{html.escape(r.output_path or "", quote=True)}">mirror</a>'
            if r.output_path
            else "—"
        )

        rows.append(
            "<tr>"
            f"<td>{html.escape(r.status)}</td>"
            f'<td><a href="{html.escape(r.url, quote=True)}">{html.escape(r.url)}</a></td>'
            f"<td>{link}</td>"
            f"<td>{html.escape(r.note or '')}</td>"
            "</tr>"
        )

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(title)}</title>
<style>
body{{font-family:Arial,Helvetica,sans-serif;max-width:1200px;margin:2rem auto;padding:0 1rem;line-height:1.45}}
table{{border-collapse:collapse;width:100%;font-size:.9rem}}
th,td{{border:1px solid #bbb;padding:.4rem;vertical-align:top}}
th{{text-align:left}}
code{{background:#eee;padding:.1rem .25rem}}
</style>
</head>
<body>
<h1>{html.escape(title)}</h1>
<p>
This site is an automatically generated, simplified HTML mirror for Slate AI ingestion.
Last run: <strong>{html.escape(generated_at)}</strong>.
</p>
<p>
The original source URL is shown on every mirrored page.
Failed refreshes preserve the last successful mirrored copy when one already exists.
</p>
<table>
<thead>
<tr>
<th>Status</th>
<th>Source URL</th>
<th>Mirror</th>
<th>Note</th>
</tr>
</thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
</body>
</html>
"""


def make_domain_landing(
    host: str,
    items: list[Result],
    generated_at: str
) -> str:

    rows: list[str] = []

    for item in sorted(
        items,
        key=lambda x: (
            (x.title or "").lower(),
            x.url.lower()
        )
    ):

        if not item.output_path:
            continue

        host_dir = (
            Path("pages")
            / safe_host_folder(host)
        )

        target = Path(item.output_path)

        rel = os.path.relpath(
            target,
            start=host_dir
        ).replace(os.sep, "/")

        label = item.title or item.url

        rows.append(
            "<li>"
            f'<a href="{html.escape(rel, quote=True)}">{html.escape(label)}</a>'
            f"<br><small>{html.escape(item.url)}</small>"
            "</li>"
        )

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(host)} — Slate knowledge mirror</title>
<style>
body{{font-family:Arial,Helvetica,sans-serif;max-width:980px;margin:2rem auto;padding:0 1rem;line-height:1.55;color:#171717}}
li{{margin-bottom:.8rem}}
small{{color:#555}}
</style>
</head>
<body>
<h1>{html.escape(host)}</h1>
<p>
Clean mirrored pages from this source domain for Slate AI ingestion.
</p>
<p>
Mirror refreshed:
<strong>{html.escape(generated_at)}</strong>.
Pages available:
<strong>{len(rows)}</strong>.
</p>
<ul>
{''.join(rows)}
</ul>
</body>
</html>
"""


def write_text(
    path: Path,
    text: str
):
    path.parent.mkdir(
        parents=True,
        exist_ok=True
    )

    path.write_text(
        text,
        encoding="utf-8"
    )


def prune_orphan_pages(
    output_dir: Path,
    keep_paths: set[str]
) -> int:

    pages_dir = output_dir / "pages"

    if not pages_dir.exists():
        return 0

    removed = 0

    for file_path in list(
        pages_dir.rglob("*")
    ):

        if not file_path.is_file():
            continue

        rel = str(
            file_path.relative_to(output_dir)
        ).replace(os.sep, "/")

        if rel not in keep_paths:
            file_path.unlink()
            removed += 1

    directories = sorted(
        [
            p
            for p in pages_dir.rglob("*")
            if p.is_dir()
        ],
        key=lambda p: len(p.parts),
        reverse=True,
    )

    for directory in directories:
        try:
            directory.rmdir()
        except OSError:
            pass

    return removed


def main() -> int:
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--sources",
        default="sources.txt"
    )

    parser.add_argument(
        "--config",
        default="config.json"
    )

    parser.add_argument(
        "--output",
        default="mirror"
    )

    args = parser.parse_args()

    sources_path = Path(args.sources)
    config = read_json(Path(args.config))
    output_dir = Path(args.output)

    output_dir.mkdir(
        parents=True,
        exist_ok=True
    )

    (output_dir / "_status").mkdir(
        parents=True,
        exist_ok=True
    )

    exact, wildcard_patterns = parse_sources(
        sources_path
    )

    rules = [
        wildcard_rule(p)
        for p in wildcard_patterns
    ]

    prior_manifest = load_existing_manifest(
        output_dir
    )

    prior_by_url = {
        item.get("url"): item
        for item in prior_manifest.get(
            "results",
            []
        )
        if item.get("url")
    }

    queue: deque[
        tuple[str, int | None]
    ] = deque()

    queued: set[str] = set()

    for u in exact:
        key = normalize_url(u)

        if key and key not in queued:
            queue.append(
                (u, None)
            )

            queued.add(key)

    for idx, rule in enumerate(rules):
        seed = rule[2]
        key = normalize_url(seed)

        if key not in queued:
            queue.append(
                (seed, idx)
            )

            queued.add(key)

    per_rule_count = [
        0
        for _ in rules
    ]

    max_per_rule = int(
        config.get(
            "max_pages_per_wildcard",
            150
        )
    )

    max_total = int(
        config.get(
            "max_total_pages",
            1200
        )
    )

    delay = float(
        config.get(
            "rate_limit_seconds",
            0.6
        )
    )

    fetcher = Fetcher(config)

    results: list[Result] = []

    docs_by_url: dict[
        str,
        tuple[str, str]
    ] = {}

    fetched_urls: set[str] = set()

    try:
        while (
            queue
            and len(fetched_urls) < max_total
        ):

            requested_url, originating_rule = queue.popleft()

            key = normalize_url(
                requested_url
            )

            if (
                not key
                or key in fetched_urls
            ):
                continue

            fetched_urls.add(key)

            p = urlsplit(
                requested_url
            )

            host = p.netloc.lower()

            if (
                "youtube.com" in host
                and p.path.startswith("/playlist")
            ):

                results.append(
                    Result(
                        url=key,
                        output_path=None,
                        status="unsupported",
                        note="YouTube playlist expansion is not enabled."
                    )
                )

                continue

            if host == "app.powerbi.com":

                results.append(
                    Result(
                        url=key,
                        output_path=None,
                        status="unsupported",
                        note="Interactive Power BI report; no reliable static text extraction."
                    )
                )

                continue

            fetched_at = utc_now()

            output_path = safe_output_path(
                key
            )

            try:
                if (
                    "youtube.com" in host
                    or host in {
                        "youtu.be",
                        "www.youtu.be"
                    }
                ):

                    yt = fetch_youtube_transcript(
                        requested_url,
                        fetcher.session
                    )

                    if not yt:
                        results.append(
                            Result(
                                url=key,
                                output_path=None,
                                status="unsupported",
                                fetched_at=fetched_at,
                                note="YouTube transcript unavailable; watch-page UI was not mirrored."
                            )
                        )

                        continue

                    title, body_html, text_chars = yt

                    document = build_document(
                        title,
                        key,
                        fetched_at,
                        body_html
                    )

                    docs_by_url[key] = (
                        output_path,
                        document
                    )

                    results.append(
                        Result(
                            url=key,
                            output_path=output_path,
                            status="ok",
                            title=title,
                            fetched_at=fetched_at,
                            fetch_method="youtube-transcript",
                            text_chars=text_chars,
                        )
                    )

                    continue

                final_url, payload, kind, http_status, method = fetcher.get(
                    requested_url
                )

                final_key = normalize_url(
                    final_url
                )

                if kind == "pdf":

                    title, body_html, text_chars = pdf_to_html(
                        payload
                        if isinstance(payload, bytes)
                        else payload.encode(),
                        final_url,
                    )

                    out = safe_output_path(
                        final_key
                    )

                    document = build_document(
                        title,
                        final_key,
                        fetched_at,
                        body_html
                    )

                    docs_by_url[
                        final_key
                    ] = (
                        out,
                        document
                    )

                    results.append(
                        Result(
                            url=final_key,
                            output_path=out,
                            status="ok",
                            title=title,
                            fetched_at=fetched_at,
                            fetch_method=method + "+pdf",
                            http_status=http_status,
                            text_chars=text_chars,
                        )
                    )

                else:

                    assert isinstance(
                        payload,
                        str
                    )

                    title, body_html, discovered, text_chars = canonicalize_html(
                        payload,
                        final_url
                    )

                    if text_chars < 80:
                        raise RuntimeError(
                            f"Too little useful text after cleaning ({text_chars} characters)"
                        )

                    out = safe_output_path(
                        final_key
                    )

                    document = build_document(
                        title,
                        final_key,
                        fetched_at,
                        body_html
                    )

                    docs_by_url[
                        final_key
                    ] = (
                        out,
                        document
                    )

                    results.append(
                        Result(
                            url=final_key,
                            output_path=out,
                            status="ok",
                            title=title,
                            fetched_at=fetched_at,
                            fetch_method=method,
                            http_status=http_status,
                            text_chars=text_chars,
                        )
                    )

                    applicable_rules = [
                        i
                        for i, rule in enumerate(rules)
                        if matches_rule(
                            final_key,
                            rule
                        )
                    ]

                    if (
                        originating_rule is not None
                        and originating_rule not in applicable_rules
                    ):

                        applicable_rules.append(
                            originating_rule
                        )

                    for href in discovered:

                        discovered_key = normalize_url(
                            href,
                            keep_query=False
                        )

                        if (
                            not discovered_key
                            or discovered_key in queued
                            or discovered_key in fetched_urls
                        ):
                            continue

                        if not is_discoverable_html_link(
                            discovered_key
                        ):
                            continue

                        matching = [
                            i
                            for i in applicable_rules
                            if matches_rule(
                                discovered_key,
                                rules[i]
                            )
                            and per_rule_count[i] < max_per_rule
                        ]

                        if not matching:
                            continue

                        chosen = matching[0]

                        queue.append(
                            (
                                discovered_key,
                                chosen
                            )
                        )

                        queued.add(
                            discovered_key
                        )

                        per_rule_count[
                            chosen
                        ] += 1

            except Exception as exc:

                prior = prior_by_url.get(
                    key
                )

                prior_path = (
                    prior.get("output_path")
                    if prior
                    else None
                )

                if (
                    prior_path
                    and (
                        output_dir
                        / prior_path
                    ).exists()
                ):

                    results.append(
                        Result(
                            url=key,
                            output_path=prior_path,
                            status="stale",
                            fetched_at=fetched_at,
                            note=(
                                "Refresh failed; retained previous copy. "
                                f"{type(exc).__name__}: {exc}"
                            ),
                        )
                    )

                else:

                    results.append(
                        Result(
                            url=key,
                            output_path=None,
                            status="failed",
                            fetched_at=fetched_at,
                            note=f"{type(exc).__name__}: {exc}",
                        )
                    )

            finally:
                time.sleep(delay)

    finally:
        fetcher.close()

    output_map = {
        u: out
        for u, (
            out,
            _doc
        ) in docs_by_url.items()
    }

    for item in results:

        if (
            item.status == "stale"
            and item.output_path
        ):

            output_map.setdefault(
                normalize_url(
                    item.url
                ),
                item.output_path
            )

    for _url, (
        out,
        doc
    ) in docs_by_url.items():

        final_doc = rewrite_links(
            doc,
            out,
            output_map,
            bool(
                config.get(
                    "keep_source_links",
                    True
                )
            ),
        )

        write_text(
            output_dir / out,
            final_doc
        )

    generated_at = utc_now()

    by_host: dict[
        str,
        list[Result]
    ] = {}

    for item in results:

        if not item.output_path:
            continue

        host = urlsplit(
            item.url
        ).netloc.lower()

        if not host:
            continue

        by_host.setdefault(
            host,
            []
        ).append(
            item
        )

    domain_landing_paths: dict[
        str,
        str
    ] = {}

    for host, items in sorted(
        by_host.items()
    ):

        landing_path = str(
            Path(
                "pages",
                safe_host_folder(host),
                "index.html"
            )
        ).replace(
            os.sep,
            "/"
        )

        domain_landing_paths[
            host
        ] = landing_path

        write_text(
            output_dir / landing_path,
            make_domain_landing(
                host,
                items,
                generated_at
            ),
        )

    keep_page_paths = {
        item.output_path
        for item in results
        if item.output_path
    }

    keep_page_paths.update(
        domain_landing_paths.values()
    )

    removed_orphans = prune_orphan_pages(
        output_dir,
        keep_page_paths
    )

    domain_counts = {
        host: sum(
            1
            for item in items
            if item.output_path
        )
        for host, items in sorted(
            by_host.items()
        )
    }

    manifest = {
        "generated_at": generated_at,
        "source_file": str(sources_path),
        "exact_source_count": len(exact),
        "wildcard_source_count": len(wildcard_patterns),
        "fetched_or_considered_count": len(results),
        "domain_counts": domain_counts,
        "domain_landing_pages": domain_landing_paths,
        "orphan_pages_removed": removed_orphans,
        "results": [
            asdict(r)
            for r in results
        ],
    }

    write_text(
        output_dir
        / "_status"
        / "manifest.json",
        json.dumps(
            manifest,
            indent=2,
            ensure_ascii=False
        ) + "\n",
    )

    write_text(
        output_dir
        / "_status"
        / "heartbeat.txt",
        f"Last automated refresh: {generated_at}\n",
    )

    write_text(
        output_dir
        / "index.html",
        make_index(
            results,
            generated_at,
            config.get(
                "site_title",
                "Slate Knowledge Mirror"
            ),
        ),
    )

    write_text(
        output_dir
        / ".nojekyll",
        ""
    )

    write_text(
        output_dir
        / "robots.txt",
        "User-agent: *\nAllow: /\n"
    )

    base = (
        config.get(
            "site_base_url",
            ""
        ).rstrip("/")
        + "/"
    )

    urls = [
        base
    ]

    for item in results:

        if item.output_path:
            urls.append(
                base
                + item.output_path
            )

    for landing_path in domain_landing_paths.values():

        urls.append(
            base
            + landing_path
        )

    sitemap = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
    ]

    for u in sorted(
        set(urls)
    ):

        sitemap.append(
            f"  <url><loc>{html.escape(u)}</loc></url>"
        )

    sitemap.append(
        "</urlset>"
    )

    write_text(
        output_dir
        / "sitemap.xml",
        "\n".join(
            sitemap
        ) + "\n",
    )

    ok = sum(
        r.status == "ok"
        for r in results
    )

    stale = sum(
        r.status == "stale"
        for r in results
    )

    failed = sum(
        r.status == "failed"
        for r in results
    )

    unsupported = sum(
        r.status == "unsupported"
        for r in results
    )

    print(
        "Mirror run complete: "
        f"{ok} ok, "
        f"{stale} stale, "
        f"{failed} failed, "
        f"{unsupported} unsupported; "
        f"{len(results)} total results; "
        f"{removed_orphans} orphan page(s) removed"
    )

    return 0 if ok + stale > 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
