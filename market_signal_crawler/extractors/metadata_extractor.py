"""
Technical metadata extractor.

Extracts non-personal technical metadata from HTTP responses and HTML:
- HTTP headers (server, content-type, caching, security headers)
- HTML meta tags (description, keywords, robots directives)
- Schema.org structured data types
- Technology fingerprints (frameworks, CDNs)
"""

import json
import logging
import re
from typing import Dict, List, Any, Optional
from datetime import datetime, timezone

from bs4 import BeautifulSoup

logger = logging.getLogger("market_signal_crawler.extractors.metadata")

# Technology detection patterns (non-PII, purely technical)
_TECH_PATTERNS = {
    "WordPress": re.compile(r"wp-content|wp-includes|wordpress", re.I),
    "React": re.compile(r"react\.production|__NEXT_DATA__|_next/", re.I),
    "Next.js": re.compile(r"__NEXT_DATA__|_next/static", re.I),
    "Vue.js": re.compile(r"vue\.runtime|__vue__|nuxt", re.I),
    "Angular": re.compile(r"ng-version|angular\.io", re.I),
    "Shopify": re.compile(r"cdn\.shopify\.com|Shopify\.theme", re.I),
    "Cloudflare": re.compile(r"cloudflare", re.I),
    "jQuery": re.compile(r"jquery[\.\-]?\d", re.I),
    "Bootstrap": re.compile(r"bootstrap\.min\.(css|js)", re.I),
    "Tailwind": re.compile(r"tailwindcss|tailwind\.config", re.I),
}

# Important HTTP headers to track (non-PII only)
_TRACKED_HEADERS = [
    "server", "x-powered-by", "content-type", "content-encoding",
    "cache-control", "x-frame-options", "strict-transport-security",
    "content-security-policy", "x-content-type-options",
    "x-xss-protection", "referrer-policy", "permissions-policy",
    "cf-ray", "x-cache", "x-cdn",
]


class MetadataExtractor:
    """Extract technical metadata signals from web responses."""

    def extract(self, url: str, html: str, headers: Optional[Dict[str, str]] = None) -> List[Dict[str, Any]]:
        """
        Extract technical metadata from a page.

        Returns a list of signal dicts.
        """
        signals: List[Dict[str, Any]] = []
        soup = BeautifulSoup(html, "html.parser")

        # 1. HTTP header signals
        if headers:
            signals.append(self._extract_headers(url, headers))

        # 2. HTML meta signals
        meta_signal = self._extract_html_meta(url, soup)
        if meta_signal:
            signals.append(meta_signal)

        # 3. Technology fingerprint
        tech_signal = self._extract_technologies(url, html)
        if tech_signal:
            signals.append(tech_signal)

        # 4. Structured data types present
        schema_signal = self._extract_schema_types(url, soup)
        if schema_signal:
            signals.append(schema_signal)

        return signals

    def _extract_headers(self, url: str, headers: Dict[str, str]) -> Dict[str, Any]:
        tracked = {}
        for key in _TRACKED_HEADERS:
            val = headers.get(key) or headers.get(key.title()) or headers.get(key.upper())
            if val:
                tracked[key] = val[:200]

        return {
            "source_url": url,
            "signal_type": "http_metadata",
            "label": "HTTP Headers",
            "value": json.dumps(tracked, ensure_ascii=False),
            "extracted_at": datetime.now(timezone.utc).isoformat(),
        }

    def _extract_html_meta(self, url: str, soup: BeautifulSoup) -> Optional[Dict[str, Any]]:
        meta_data = {}

        # Standard meta tags
        for tag in soup.find_all("meta"):
            name = tag.get("name", "").lower() or tag.get("property", "").lower()
            content = tag.get("content", "")
            if name in ("description", "keywords", "robots", "generator", "theme-color",
                        "viewport", "og:type", "og:site_name", "og:locale",
                        "twitter:card", "twitter:site"):
                meta_data[name] = content[:500]

        # Title
        title_tag = soup.find("title")
        if title_tag and title_tag.string:
            meta_data["title"] = title_tag.string.strip()[:500]

        # Language
        html_tag = soup.find("html")
        if html_tag and html_tag.get("lang"):
            meta_data["language"] = html_tag["lang"][:10]

        if not meta_data:
            return None

        return {
            "source_url": url,
            "signal_type": "html_metadata",
            "label": "HTML Meta Tags",
            "value": json.dumps(meta_data, ensure_ascii=False),
            "extracted_at": datetime.now(timezone.utc).isoformat(),
        }

    def _extract_technologies(self, url: str, html: str) -> Optional[Dict[str, Any]]:
        detected = []
        # Only check first 50KB to limit processing
        sample = html[:51200]
        for tech_name, pattern in _TECH_PATTERNS.items():
            if pattern.search(sample):
                detected.append(tech_name)

        if not detected:
            return None

        return {
            "source_url": url,
            "signal_type": "technology_fingerprint",
            "label": "Detected Technologies",
            "value": json.dumps(detected),
            "extracted_at": datetime.now(timezone.utc).isoformat(),
        }

    def _extract_schema_types(self, url: str, soup: BeautifulSoup) -> Optional[Dict[str, Any]]:
        schema_types = set()
        for script in soup.find_all("script", type="application/ld+json"):
            try:
                data = json.loads(script.string or "")
                items = data if isinstance(data, list) else [data]
                for item in items:
                    t = item.get("@type")
                    if t:
                        if isinstance(t, list):
                            schema_types.update(t)
                        else:
                            schema_types.add(t)
            except (json.JSONDecodeError, TypeError):
                continue

        # Also check microdata itemtype attributes
        for elem in soup.find_all(attrs={"itemtype": True}):
            schema_types.add(elem["itemtype"].split("/")[-1])

        if not schema_types:
            return None

        return {
            "source_url": url,
            "signal_type": "schema_types",
            "label": "Structured Data Types",
            "value": json.dumps(sorted(schema_types)),
            "extracted_at": datetime.now(timezone.utc).isoformat(),
        }
