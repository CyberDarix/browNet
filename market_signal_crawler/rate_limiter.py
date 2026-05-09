"""
Per-domain rate limiter using a token-bucket algorithm.

Ensures we never overwhelm any single server. The delay is the maximum of:
  1. The default crawl delay from config
  2. The Crawl-delay directive from the domain's robots.txt
"""

import asyncio
import logging
import time
from typing import Dict, Optional

logger = logging.getLogger("market_signal_crawler.rate_limiter")


class DomainRateLimiter:
    """Token-bucket style per-domain rate limiter."""

    def __init__(self, default_delay: float = 2.0):
        self.default_delay = default_delay
        # domain -> last_request_timestamp
        self._last_request: Dict[str, float] = {}
        # domain -> enforced delay
        self._domain_delay: Dict[str, float] = {}
        self._locks: Dict[str, asyncio.Lock] = {}

    def set_domain_delay(self, domain: str, robots_delay: Optional[float]) -> None:
        """Set domain delay, respecting the stricter of config vs robots.txt."""
        if robots_delay is not None:
            self._domain_delay[domain] = max(self.default_delay, robots_delay)
        else:
            self._domain_delay[domain] = self.default_delay

    def _get_lock(self, domain: str) -> asyncio.Lock:
        if domain not in self._locks:
            self._locks[domain] = asyncio.Lock()
        return self._locks[domain]

    async def wait(self, domain: str) -> None:
        """Wait until it is safe to send the next request to *domain*."""
        lock = self._get_lock(domain)
        async with lock:
            delay = self._domain_delay.get(domain, self.default_delay)
            last = self._last_request.get(domain, 0.0)
            elapsed = time.time() - last
            if elapsed < delay:
                wait_time = delay - elapsed
                logger.debug("Rate-limiting %s: waiting %.2fs", domain, wait_time)
                await asyncio.sleep(wait_time)
            self._last_request[domain] = time.time()

    def reset(self) -> None:
        self._last_request.clear()
        self._domain_delay.clear()
        self._locks.clear()
