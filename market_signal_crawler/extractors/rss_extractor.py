"""
RSS / Atom feed extractor.

Fetches and parses official RSS/Atom feeds to extract structured article
metadata as market signals (titles, publication dates, categories, summaries).
"""

import logging
import xml.etree.ElementTree as ET
from typing import Dict, List, Any, Optional
from datetime import datetime, timezone

logger = logging.getLogger("market_signal_crawler.extractors.rss")

# Common RSS/Atom namespaces
_ATOM_NS = "{http://www.w3.org/2005/Atom}"
_DC_NS = "{http://purl.org/dc/elements/1.1/}"
_CONTENT_NS = "{http://purl.org/rss/1.0/modules/content/}"
_MEDIA_NS = "{http://search.yahoo.com/mrss/}"


class RSSExtractor:
    """Parse RSS 2.0 and Atom feeds into structured market signals."""

    def extract(self, feed_url: str, xml_content: str) -> List[Dict[str, Any]]:
        """
        Parse an RSS or Atom feed and return signal dicts.

        Each signal contains: source_url, title, summary, published_at,
        categories, link, signal_type, extracted_at.
        """
        signals: List[Dict[str, Any]] = []
        try:
            root = ET.fromstring(xml_content)
        except ET.ParseError as exc:
            logger.warning("Failed to parse feed %s: %s", feed_url, exc)
            return signals

        # Detect feed type
        tag = root.tag.lower().split("}")[-1] if "}" in root.tag else root.tag.lower()

        if tag == "rss":
            signals = self._parse_rss(feed_url, root)
        elif tag == "feed":
            signals = self._parse_atom(feed_url, root)
        elif tag == "rdf":
            signals = self._parse_rss(feed_url, root)  # RSS 1.0 / RDF
        else:
            logger.warning("Unknown feed format for %s: root tag = %s", feed_url, root.tag)

        return signals

    def _parse_rss(self, feed_url: str, root: ET.Element) -> List[Dict[str, Any]]:
        signals = []
        channel = root.find("channel")
        if channel is None:
            # RSS 1.0 / RDF may not have channel wrapping items
            items = root.findall("item") or root.findall(f"{{http://purl.org/rss/1.0/}}item")
        else:
            items = channel.findall("item")

        for item in items:
            title = self._text(item, "title")
            link = self._text(item, "link")
            description = self._text(item, "description")
            pub_date = self._text(item, "pubDate") or self._text(item, f"{_DC_NS}date")
            categories = [cat.text for cat in item.findall("category") if cat.text]

            if not title:
                continue

            signals.append({
                "source_url": feed_url,
                "signal_type": "rss_article",
                "title": title[:1000],
                "summary": (description or "")[:2000],
                "link": link or feed_url,
                "published_at": pub_date or "",
                "categories": ",".join(categories)[:500],
                "extracted_at": datetime.now(timezone.utc).isoformat(),
            })

        return signals

    def _parse_atom(self, feed_url: str, root: ET.Element) -> List[Dict[str, Any]]:
        signals = []
        entries = root.findall(f"{_ATOM_NS}entry")

        for entry in entries:
            title = self._text(entry, f"{_ATOM_NS}title")
            # Atom link may be in an attribute
            link_elem = entry.find(f"{_ATOM_NS}link[@rel='alternate']") or entry.find(f"{_ATOM_NS}link")
            link = link_elem.get("href", "") if link_elem is not None else ""
            summary = self._text(entry, f"{_ATOM_NS}summary") or self._text(entry, f"{_ATOM_NS}content")
            updated = self._text(entry, f"{_ATOM_NS}updated") or self._text(entry, f"{_ATOM_NS}published")
            categories = [cat.get("term", "") for cat in entry.findall(f"{_ATOM_NS}category") if cat.get("term")]

            if not title:
                continue

            signals.append({
                "source_url": feed_url,
                "signal_type": "rss_article",
                "title": title[:1000],
                "summary": (summary or "")[:2000],
                "link": link or feed_url,
                "published_at": updated or "",
                "categories": ",".join(categories)[:500],
                "extracted_at": datetime.now(timezone.utc).isoformat(),
            })

        return signals

    @staticmethod
    def _text(parent: ET.Element, tag: str) -> Optional[str]:
        elem = parent.find(tag)
        if elem is not None and elem.text:
            return elem.text.strip()
        return None
