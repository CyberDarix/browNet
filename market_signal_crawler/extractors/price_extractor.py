"""
Price signal extractor.

Extracts publicly visible price data from web pages using:
- JSON-LD structured data (schema.org Product / Offer)
- Open Graph meta tags
- Microdata attributes
- Common CSS patterns for price display
"""

import re
import json
import logging
from typing import Dict, List, Optional, Any
from datetime import datetime, timezone

from bs4 import BeautifulSoup

logger = logging.getLogger("market_signal_crawler.extractors.price")

# Currency symbols and codes
_CURRENCY_SYMBOLS = {
    "$": "USD", "€": "EUR", "£": "GBP", "¥": "JPY",
    "CHF": "CHF", "CAD": "CAD", "AUD": "AUD",
}
_PRICE_RE = re.compile(
    r"(?P<currency>[€$£¥])\s*(?P<amount>[\d,.\s]+[\d])"
    r"|(?P<amount2>[\d,.\s]+[\d])\s*(?P<currency2>[€$£¥])"
    r"|(?P<amount3>[\d,.\s]+[\d])\s*(?P<code>USD|EUR|GBP|JPY|CHF|CAD|AUD|BTC|ETH)",
    re.IGNORECASE,
)


class PriceExtractor:
    """Extract price signals from public web pages."""

    def extract(self, url: str, html: str) -> List[Dict[str, Any]]:
        """
        Extract all price signals from the given HTML.

        Returns a list of dicts with keys:
            source_url, label, price, currency, extracted_at, method
        """
        signals: List[Dict[str, Any]] = []
        soup = BeautifulSoup(html, "html.parser")

        # 1. JSON-LD structured data
        signals.extend(self._extract_jsonld(url, soup))

        # 2. Open Graph price tags
        signals.extend(self._extract_opengraph(url, soup))

        # 3. Microdata (itemprop="price")
        signals.extend(self._extract_microdata(url, soup))

        # 4. Heuristic CSS-based extraction (last resort)
        if not signals:
            signals.extend(self._extract_heuristic(url, soup))

        return signals

    def _extract_jsonld(self, url: str, soup: BeautifulSoup) -> List[Dict[str, Any]]:
        results = []
        for script in soup.find_all("script", type="application/ld+json"):
            try:
                data = json.loads(script.string or "")
                items = data if isinstance(data, list) else [data]
                for item in items:
                    results.extend(self._parse_schema_item(url, item))
            except (json.JSONDecodeError, TypeError):
                continue
        return results

    def _parse_schema_item(self, url: str, item: Dict) -> List[Dict[str, Any]]:
        results = []
        item_type = item.get("@type", "")

        # Handle Product, Offer, etc.
        if item_type in ("Product", "IndividualProduct"):
            offers = item.get("offers", {})
            if isinstance(offers, dict):
                offers = [offers]
            for offer in offers if isinstance(offers, list) else []:
                price = offer.get("price") or offer.get("lowPrice")
                currency = offer.get("priceCurrency", "")
                if price:
                    results.append(self._make_signal(
                        url=url,
                        label=item.get("name", "Unknown Product"),
                        price=str(price),
                        currency=currency,
                        method="json-ld",
                    ))

        # Recurse into nested items
        for key, value in item.items():
            if isinstance(value, dict) and "@type" in value:
                results.extend(self._parse_schema_item(url, value))
            elif isinstance(value, list):
                for sub in value:
                    if isinstance(sub, dict) and "@type" in sub:
                        results.extend(self._parse_schema_item(url, sub))

        return results

    def _extract_opengraph(self, url: str, soup: BeautifulSoup) -> List[Dict[str, Any]]:
        results = []
        price_tag = soup.find("meta", property="og:price:amount") or soup.find("meta", attrs={"name": "og:price:amount"})
        currency_tag = soup.find("meta", property="og:price:currency") or soup.find("meta", attrs={"name": "og:price:currency"})
        title_tag = soup.find("meta", property="og:title")

        if price_tag and price_tag.get("content"):
            results.append(self._make_signal(
                url=url,
                label=(title_tag.get("content", "Unknown") if title_tag else "Unknown"),
                price=price_tag["content"],
                currency=(currency_tag["content"] if currency_tag and currency_tag.get("content") else ""),
                method="opengraph",
            ))
        return results

    def _extract_microdata(self, url: str, soup: BeautifulSoup) -> List[Dict[str, Any]]:
        results = []
        for elem in soup.find_all(attrs={"itemprop": "price"}):
            price = elem.get("content") or elem.get_text(strip=True)
            currency_elem = elem.find_parent().find(attrs={"itemprop": "priceCurrency"}) if elem.find_parent() else None
            currency = ""
            if currency_elem:
                currency = currency_elem.get("content") or currency_elem.get_text(strip=True)
            name_elem = soup.find(attrs={"itemprop": "name"})
            label = name_elem.get("content", name_elem.get_text(strip=True)) if name_elem else "Unknown"

            if price:
                results.append(self._make_signal(
                    url=url, label=label, price=price, currency=currency, method="microdata",
                ))
        return results

    def _extract_heuristic(self, url: str, soup: BeautifulSoup) -> List[Dict[str, Any]]:
        """Heuristic fallback: scan visible text for price patterns."""
        results = []
        text = soup.get_text(separator=" ", strip=True)
        # Limit to first 5000 chars to avoid noise
        text = text[:5000]
        seen = set()
        for match in _PRICE_RE.finditer(text):
            amount = match.group("amount") or match.group("amount2") or match.group("amount3") or ""
            currency = match.group("currency") or match.group("currency2") or match.group("code") or ""
            key = f"{amount.strip()}_{currency.strip()}"
            if key not in seen:
                seen.add(key)
                results.append(self._make_signal(
                    url=url, label="Heuristic Price", price=amount.strip(),
                    currency=_CURRENCY_SYMBOLS.get(currency.strip(), currency.strip()),
                    method="heuristic",
                ))
        return results[:10]  # cap at 10

    @staticmethod
    def _make_signal(url: str, label: str, price: str, currency: str, method: str) -> Dict[str, Any]:
        return {
            "source_url": url,
            "signal_type": "price",
            "label": label[:500],
            "value": price,
            "currency": currency[:10],
            "extraction_method": method,
            "extracted_at": datetime.now(timezone.utc).isoformat(),
        }
