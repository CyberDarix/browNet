"""
robots.txt compliance module.

Before ANY request, the crawler MUST check the target domain's robots.txt.
This module caches parsed robots.txt files and exposes a simple
``is_allowed(url)`` API.
"""

import asyncio
import logging
import time
from typing import Dict, Optional, Tuple
from urllib.parse import urlparse
from urllib.robotparser import RobotFileParser

import aiohttp

logger = logging.getLogger("market_signal_crawler.robots")


class RobotsChecker:
    """Async robots.txt checker with TTL cache."""

    def __init__(self, user_agent: str, cache_ttl: int = 3600, timeout: int = 10):
        self.user_agent = user_agent
        self.cache_ttl = cache_ttl
        self.timeout = timeout
        # domain -> (RobotFileParser, timestamp, crawl_delay)
        self._cache: Dict[str, Tuple[RobotFileParser, float, Optional[float]]] = {}
        self._locks: Dict[str, asyncio.Lock] = {}

    def _get_lock(self, domain: str) -> asyncio.Lock:
        if domain not in self._locks:
            self._locks[domain] = asyncio.Lock()
        return self._locks[domain]

    async def _fetch_robots(self, domain: str, scheme: str, session: aiohttp.ClientSession) -> Tuple[RobotFileParser, Optional[float]]:
        """Fetch and parse robots.txt for a domain."""
        robots_url = f"{scheme}://{domain}/robots.txt"
        rp = RobotFileParser()
        rp.set_url(robots_url)
        crawl_delay: Optional[float] = None

        try:
            async with session.get(robots_url, timeout=aiohttp.ClientTimeout(total=self.timeout)) as resp:
                if resp.status == 200:
                    text = await resp.text()
                    rp.parse(text.splitlines())
                    # Extract crawl-delay
                    delay = rp.crawl_delay(self.user_agent)
                    if delay is not None:
                        crawl_delay = float(delay)
                    logger.info("Loaded robots.txt for %s (%d bytes)", domain, len(text))
                else:
                    # No robots.txt or error -> allow all (standard behaviour)
                    rp.allow_all = True
                    logger.info("No robots.txt for %s (HTTP %d) - allowing all", domain, resp.status)
        except Exception as exc:
            # Network error -> be conservative, allow all (RFC standard)
            rp.allow_all = True
            logger.warning("Failed to fetch robots.txt for %s: %s", domain, exc)

        return rp, crawl_delay

    async def is_allowed(self, url: str, session: aiohttp.ClientSession) -> bool:
        """Check whether the given URL is allowed by robots.txt."""
        parsed = urlparse(url)
        domain = parsed.netloc
        scheme = parsed.scheme or "https"

        lock = self._get_lock(domain)
        async with lock:
            cached = self._cache.get(domain)
            if cached and (time.time() - cached[1]) < self.cache_ttl:
                rp = cached[0]
            else:
                rp, crawl_delay = await self._fetch_robots(domain, scheme, session)
                self._cache[domain] = (rp, time.time(), crawl_delay)

        try:
            return rp.can_fetch(self.user_agent, url)
        except Exception:
            # If parsing fails, deny access to be safe
            return False

    def get_crawl_delay(self, domain: str) -> Optional[float]:
        """Return the crawl-delay specified in robots.txt, or None."""
        cached = self._cache.get(domain)
        if cached:
            return cached[2]
        return None

    def clear_cache(self) -> None:
        self._cache.clear()
        self._locks.clear()
