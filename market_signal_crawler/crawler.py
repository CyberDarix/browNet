"""
Main crawler orchestrator.

Coordinates the ethical crawl swarm:
1. Checks robots.txt before every request
2. Applies per-domain rate limiting
3. Runs all extractors on fetched pages
4. Filters PII through the GDPR module
5. Stores clean signals in the SQL database
"""

import asyncio
import json
import logging
import time
from typing import Dict, List, Optional, Set
from urllib.parse import urlparse

import aiohttp

from .config import CrawlerConfig
from .robots_checker import RobotsChecker
from .rate_limiter import DomainRateLimiter
from .gdpr_filter import GDPRFilter
from .database import SignalDatabase
from .extractors.price_extractor import PriceExtractor
from .extractors.rss_extractor import RSSExtractor
from .extractors.metadata_extractor import MetadataExtractor
from .extractors.trend_extractor import TrendExtractor

logger = logging.getLogger("market_signal_crawler.crawler")


class MarketSignalCrawler:
    """
    Ethical market signal extraction swarm.

    Orchestrates concurrent crawling of public sources while strictly
    respecting robots.txt, rate limits, and GDPR requirements.
    """

    def __init__(self, config: Optional[CrawlerConfig] = None):
        self.config = config or CrawlerConfig()

        # Core components
        self.robots = RobotsChecker(
            user_agent=self.config.user_agent,
            cache_ttl=self.config.robots_cache_ttl,
            timeout=self.config.request_timeout,
        )
        self.rate_limiter = DomainRateLimiter(
            default_delay=self.config.default_crawl_delay,
        )
        self.gdpr = GDPRFilter(strict=self.config.gdpr_strict)
        self.db = SignalDatabase(db_path=self.config.db_path)

        # Extractors
        self.price_extractor = PriceExtractor()
        self.rss_extractor = RSSExtractor()
        self.metadata_extractor = MetadataExtractor()
        self.trend_extractor = TrendExtractor()

        # State
        self._session_id: Optional[int] = None
        self._pages_crawled = 0
        self._signals_stored = 0
        self._visited: Set[str] = set()
        self._semaphore: Optional[asyncio.Semaphore] = None

    async def run(self) -> Dict:
        """
        Execute a full crawl session.

        Returns a summary dict with stats.
        """
        logger.info("=== Market Signal Crawler starting ===")
        logger.info("Config: max_concurrent=%d, delay=%.1fs, gdpr_strict=%s",
                     self.config.max_concurrent_requests,
                     self.config.default_crawl_delay,
                     self.config.gdpr_strict)

        self.db.connect()
        self._session_id = self.db.start_session(
            config_snapshot=json.dumps({
                "user_agent": self.config.user_agent,
                "max_concurrent": self.config.max_concurrent_requests,
                "crawl_delay": self.config.default_crawl_delay,
                "gdpr_strict": self.config.gdpr_strict,
            })
        )
        self._semaphore = asyncio.Semaphore(self.config.max_concurrent_requests)
        self._pages_crawled = 0
        self._signals_stored = 0
        self._visited.clear()

        start_time = time.time()

        try:
            connector = aiohttp.TCPConnector(
                limit=self.config.max_concurrent_requests,
                ttl_dns_cache=300,
                ssl=False,  # Allow both http and https
            )
            timeout = aiohttp.ClientTimeout(total=self.config.request_timeout)
            headers = {"User-Agent": self.config.user_agent}

            async with aiohttp.ClientSession(
                connector=connector, timeout=timeout, headers=headers
            ) as session:
                tasks = []

                # Phase 1: RSS feeds (highest value, lowest impact)
                logger.info("Phase 1: Fetching %d RSS feeds", len(self.config.rss_feeds))
                for feed_url in self.config.rss_feeds:
                    tasks.append(self._crawl_rss(session, feed_url))

                # Phase 2: Price seed URLs
                logger.info("Phase 2: Crawling %d price seed URLs", len(self.config.price_seed_urls))
                for url in self.config.price_seed_urls:
                    tasks.append(self._crawl_page(session, url, extract_prices=True))

                # Phase 3: Trend / media seed URLs
                logger.info("Phase 3: Crawling %d trend seed URLs", len(self.config.trend_seed_urls))
                for url in self.config.trend_seed_urls:
                    tasks.append(self._crawl_page(session, url, extract_trends=True))

                # Run all tasks with bounded concurrency
                results = await asyncio.gather(*tasks, return_exceptions=True)

                for result in results:
                    if isinstance(result, Exception):
                        logger.error("Task failed: %s", result)

        except Exception as exc:
            logger.error("Crawl session failed: %s", exc)
        finally:
            elapsed = time.time() - start_time
            self.db.end_session(
                self._session_id,
                pages=self._pages_crawled,
                signals=self._signals_stored,
            )
            self.db.close()

        summary = {
            "session_id": self._session_id,
            "pages_crawled": self._pages_crawled,
            "signals_stored": self._signals_stored,
            "elapsed_seconds": round(elapsed, 2),
            "gdpr_filter_stats": self.gdpr.stats,
        }
        logger.info("=== Crawl complete: %s ===", summary)
        return summary

    async def _crawl_rss(self, session: aiohttp.ClientSession, feed_url: str) -> None:
        """Fetch and extract signals from an RSS feed."""
        domain = urlparse(feed_url).netloc

        if self._is_blocked(domain):
            logger.info("Skipping blocked domain: %s", domain)
            return

        async with self._semaphore:
            # Check robots.txt
            allowed = await self.robots.is_allowed(feed_url, session)
            if not allowed:
                logger.info("robots.txt disallows: %s", feed_url)
                self.db.log_crawl(
                    self._session_id, feed_url, domain,
                    status_code=0, content_length=0,
                    robots_allowed=False, signals_found=0,
                )
                return

            # Apply rate limit
            self._apply_robots_delay(domain)
            await self.rate_limiter.wait(domain)

            try:
                async with session.get(feed_url) as resp:
                    if resp.status != 200:
                        logger.warning("RSS feed %s returned %d", feed_url, resp.status)
                        self.db.log_crawl(
                            self._session_id, feed_url, domain,
                            status_code=resp.status, content_length=0,
                            robots_allowed=True, signals_found=0,
                        )
                        return

                    content = await resp.text()
                    self._pages_crawled += 1

                    # Extract RSS articles
                    articles = self.rss_extractor.extract(feed_url, content)

                    # GDPR filter on summaries
                    clean_articles = []
                    for article in articles:
                        filtered_title = self.gdpr.filter_text(article.get("title", ""))
                        filtered_summary = self.gdpr.filter_text(article.get("summary", ""))
                        if filtered_title is None:
                            continue  # PII in title, skip entire article
                        article["title"] = filtered_title
                        article["summary"] = filtered_summary or ""
                        clean_articles.append(article)

                    # Store
                    if clean_articles:
                        count = self.db.store_rss_articles_batch(self._session_id, clean_articles)
                        self._signals_stored += count
                        logger.info("RSS %s: stored %d articles", feed_url, count)

                    self.db.log_crawl(
                        self._session_id, feed_url, domain,
                        status_code=resp.status, content_length=len(content),
                        robots_allowed=True, signals_found=len(clean_articles),
                    )

            except Exception as exc:
                logger.error("Error fetching RSS %s: %s", feed_url, exc)

    async def _crawl_page(
        self,
        session: aiohttp.ClientSession,
        url: str,
        extract_prices: bool = False,
        extract_trends: bool = False,
    ) -> None:
        """Fetch a page and extract market signals."""
        domain = urlparse(url).netloc

        if url in self._visited:
            return
        self._visited.add(url)

        if self._is_blocked(domain):
            logger.info("Skipping blocked domain: %s", domain)
            return

        async with self._semaphore:
            # Check robots.txt
            allowed = await self.robots.is_allowed(url, session)
            if not allowed:
                logger.info("robots.txt disallows: %s", url)
                self.db.log_crawl(
                    self._session_id, url, domain,
                    status_code=0, content_length=0,
                    robots_allowed=False, signals_found=0,
                )
                return

            # Apply rate limit
            self._apply_robots_delay(domain)
            await self.rate_limiter.wait(domain)

            try:
                async with session.get(url) as resp:
                    if resp.status != 200:
                        logger.warning("Page %s returned %d", url, resp.status)
                        self.db.log_crawl(
                            self._session_id, url, domain,
                            status_code=resp.status, content_length=0,
                            robots_allowed=True, signals_found=0,
                        )
                        return

                    html = await resp.text()
                    headers = {k.lower(): v for k, v in resp.headers.items()}
                    self._pages_crawled += 1

                    all_signals: List[Dict] = []

                    # Always extract metadata
                    meta_signals = self.metadata_extractor.extract(url, html, headers)
                    all_signals.extend(meta_signals)

                    # Price extraction
                    if extract_prices:
                        price_signals = self.price_extractor.extract(url, html)
                        all_signals.extend(price_signals)

                    # Trend extraction
                    if extract_trends:
                        trend_signals = self.trend_extractor.extract(url, html)
                        all_signals.extend(trend_signals)

                    # GDPR filter all signals
                    clean_signals = []
                    for signal in all_signals:
                        # Filter the value field
                        filtered_value = self.gdpr.filter_text(signal.get("value", ""))
                        if filtered_value is None:
                            continue
                        signal["value"] = filtered_value

                        # Filter the label field
                        filtered_label = self.gdpr.filter_text(signal.get("label", ""))
                        if filtered_label is None:
                            continue
                        signal["label"] = filtered_label

                        clean_signals.append(signal)

                    # Store
                    if clean_signals:
                        count = self.db.store_signals_batch(self._session_id, clean_signals)
                        self._signals_stored += count

                    self.db.log_crawl(
                        self._session_id, url, domain,
                        status_code=resp.status, content_length=len(html),
                        robots_allowed=True, signals_found=len(clean_signals),
                    )
                    logger.info("Page %s: %d signals extracted", url, len(clean_signals))

            except Exception as exc:
                logger.error("Error crawling %s: %s", url, exc)

    def _is_blocked(self, domain: str) -> bool:
        """Check if the domain is in the blocklist."""
        for blocked in self.config.blocked_domains:
            if domain.endswith(blocked):
                return True
        return False

    def _apply_robots_delay(self, domain: str) -> None:
        """Set the rate limiter delay based on robots.txt crawl-delay."""
        robots_delay = self.robots.get_crawl_delay(domain)
        self.rate_limiter.set_domain_delay(domain, robots_delay)


def run_crawler(config: Optional[CrawlerConfig] = None) -> Dict:
    """Convenience function to run the crawler synchronously."""
    crawler = MarketSignalCrawler(config)
    return asyncio.run(crawler.run())


if __name__ == "__main__":
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )
    result = run_crawler()
    print(json.dumps(result, indent=2))
