"""
Public media trend extractor.

Extracts trend signals from public web pages:
- Headline analysis and keyword frequency
- Trending topic indicators
- Public engagement metrics (visible counts only)
- Sentiment polarity (basic lexicon-based)
"""

import re
import logging
from typing import Dict, List, Any
from collections import Counter
from datetime import datetime, timezone

from bs4 import BeautifulSoup

logger = logging.getLogger("market_signal_crawler.extractors.trend")

# Basic sentiment lexicons (market-relevant)
_POSITIVE_WORDS = frozenset([
    "growth", "surge", "rally", "gain", "profit", "bullish", "rise", "boost",
    "optimism", "recovery", "expansion", "hausse", "croissance", "positif",
    "record", "breakthrough", "innovation", "upgrade", "outperform",
])

_NEGATIVE_WORDS = frozenset([
    "crash", "decline", "loss", "bearish", "drop", "fall", "recession",
    "crisis", "downturn", "plunge", "slump", "baisse", "chute", "negatif",
    "risk", "warning", "layoff", "bankruptcy", "default", "inflation",
])

# Noise words to exclude from keyword analysis
_STOP_WORDS = frozenset([
    "the", "a", "an", "is", "are", "was", "were", "be", "been", "being",
    "have", "has", "had", "do", "does", "did", "will", "would", "could",
    "should", "may", "might", "shall", "can", "to", "of", "in", "for",
    "on", "with", "at", "by", "from", "as", "into", "through", "during",
    "before", "after", "above", "below", "between", "under", "again",
    "further", "then", "once", "here", "there", "when", "where", "why",
    "how", "all", "each", "every", "both", "few", "more", "most", "other",
    "some", "such", "no", "nor", "not", "only", "own", "same", "so",
    "than", "too", "very", "and", "but", "or", "if", "le", "la", "les",
    "de", "du", "des", "un", "une", "et", "en", "est", "que", "qui",
    "ce", "se", "ne", "pas", "par", "sur", "au", "aux", "pour", "dans",
    "this", "that", "it", "its", "he", "she", "they", "we", "you", "i",
])


class TrendExtractor:
    """Extract trend and sentiment signals from public web content."""

    def extract(self, url: str, html: str) -> List[Dict[str, Any]]:
        """
        Extract trend signals from a web page.

        Returns signal dicts for: headlines, top keywords, sentiment score.
        """
        signals: List[Dict[str, Any]] = []
        soup = BeautifulSoup(html, "html.parser")

        # 1. Headlines extraction
        headlines = self._extract_headlines(soup)
        if headlines:
            signals.append({
                "source_url": url,
                "signal_type": "headlines",
                "label": f"Top {len(headlines)} Headlines",
                "value": " | ".join(headlines),
                "extracted_at": datetime.now(timezone.utc).isoformat(),
            })

        # 2. Keyword frequency analysis
        keywords = self._extract_keywords(soup)
        if keywords:
            kw_str = ", ".join(f"{word}:{count}" for word, count in keywords)
            signals.append({
                "source_url": url,
                "signal_type": "keyword_frequency",
                "label": "Top Keywords",
                "value": kw_str,
                "extracted_at": datetime.now(timezone.utc).isoformat(),
            })

        # 3. Sentiment analysis
        sentiment = self._compute_sentiment(soup)
        signals.append({
            "source_url": url,
            "signal_type": "sentiment",
            "label": "Page Sentiment",
            "value": f"{sentiment['score']:.3f}",
            "positive_count": sentiment["positive"],
            "negative_count": sentiment["negative"],
            "extracted_at": datetime.now(timezone.utc).isoformat(),
        })

        return signals

    def _extract_headlines(self, soup: BeautifulSoup) -> List[str]:
        """Extract text from h1-h3 tags and prominent links."""
        headlines = []
        for tag in soup.find_all(["h1", "h2", "h3"]):
            text = tag.get_text(strip=True)
            if text and len(text) > 10:
                headlines.append(text[:300])
        # Also consider article titles in <article> or role=article
        for article in soup.find_all("article"):
            title = article.find(["h1", "h2", "h3", "h4"])
            if title:
                text = title.get_text(strip=True)
                if text and text not in headlines:
                    headlines.append(text[:300])
        return headlines[:30]

    def _extract_keywords(self, soup: BeautifulSoup, top_n: int = 20) -> List[tuple]:
        """
        Extract top keywords by frequency from visible text.
        Excludes stop words and short tokens.
        """
        # Remove script and style content
        for tag in soup(["script", "style", "nav", "footer", "header"]):
            tag.decompose()

        text = soup.get_text(separator=" ", strip=True).lower()
        words = re.findall(r"\b[a-zA-Z\u00C0-\u017F]{4,}\b", text)
        filtered = [w for w in words if w not in _STOP_WORDS]
        counter = Counter(filtered)
        return counter.most_common(top_n)

    def _compute_sentiment(self, soup: BeautifulSoup) -> Dict[str, Any]:
        """Basic lexicon-based sentiment scoring."""
        text = soup.get_text(separator=" ", strip=True).lower()
        words = set(re.findall(r"\b[a-z]{3,}\b", text))

        pos = len(words & _POSITIVE_WORDS)
        neg = len(words & _NEGATIVE_WORDS)
        total = pos + neg

        if total == 0:
            score = 0.0
        else:
            score = (pos - neg) / total  # -1.0 to +1.0

        return {"score": score, "positive": pos, "negative": neg}
