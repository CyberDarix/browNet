"""
Signal extractors for market data collection.

Each extractor focuses on a specific type of public market signal:
- PriceExtractor: price variations from public financial pages
- RSSExtractor: articles and signals from official RSS feeds
- MetadataExtractor: technical metadata (headers, structured data)
- TrendExtractor: public media trends and sentiment signals
"""

from .price_extractor import PriceExtractor
from .rss_extractor import RSSExtractor
from .metadata_extractor import MetadataExtractor
from .trend_extractor import TrendExtractor

__all__ = [
    "PriceExtractor",
    "RSSExtractor",
    "MetadataExtractor",
    "TrendExtractor",
]
