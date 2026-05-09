"""
Configuration for the market signal crawler.
All sensitive values are loaded from environment variables.
"""

import os
from dataclasses import dataclass, field
from typing import List


@dataclass
class CrawlerConfig:
    """Central configuration for the ethical market signal crawler."""

    # --- Database (SQLite by default, override for remote SQL) ---
    db_path: str = os.environ.get("CRAWLER_DB_PATH", "market_signals.db")

    # --- Crawling behaviour ---
    user_agent: str = "MarketSignalBot/1.0 (+https://brownet.net/bot; ethical-crawler)"
    max_concurrent_requests: int = int(os.environ.get("CRAWLER_MAX_CONCURRENT", "10"))
    default_crawl_delay: float = float(os.environ.get("CRAWLER_DELAY", "2.0"))
    request_timeout: int = int(os.environ.get("CRAWLER_TIMEOUT", "15"))
    max_retries: int = 3
    max_pages_per_domain: int = int(os.environ.get("CRAWLER_MAX_PAGES_DOMAIN", "50"))
    robots_cache_ttl: int = 3600  # seconds

    # --- GDPR / Privacy ---
    gdpr_strict: bool = True  # when True, aggressively filter PII

    # --- RSS feed sources (public, official) ---
    rss_feeds: List[str] = field(default_factory=lambda: [
        "https://feeds.bbci.co.uk/news/business/rss.xml",
        "https://rss.nytimes.com/services/xml/rss/nyt/Business.xml",
        "https://www.lemonde.fr/economie/rss_full.xml",
        "https://www.reuters.com/rssFeed/businessNews",
        "https://feeds.feedburner.com/TechCrunch/",
        "https://hnrss.org/frontpage",
    ])

    # --- Price tracking seed URLs (public pricing pages) ---
    price_seed_urls: List[str] = field(default_factory=lambda: [
        "https://www.coingecko.com/",
        "https://finance.yahoo.com/trending-tickers/",
        "https://www.investing.com/commodities/",
    ])

    # --- Trend / media seed URLs ---
    trend_seed_urls: List[str] = field(default_factory=lambda: [
        "https://trends.google.com/trending?geo=FR",
        "https://news.ycombinator.com/",
        "https://www.reddit.com/r/worldnews/.json",
    ])

    # --- Domains to never crawl ---
    blocked_domains: List[str] = field(default_factory=lambda: [
        "facebook.com",
        "instagram.com",
        "twitter.com",
        "x.com",
        "linkedin.com",
        "tiktok.com",
    ])
