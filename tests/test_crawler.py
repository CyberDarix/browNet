"""
Tests for the market_signal_crawler package.

Covers: GDPR filter, extractors, database, robots checker, rate limiter.
"""

import json
import os
import sqlite3
import tempfile
import time
import unittest
import asyncio
from unittest.mock import AsyncMock, MagicMock, patch
from datetime import datetime, timezone

# Module imports
from market_signal_crawler.config import CrawlerConfig
from market_signal_crawler.gdpr_filter import GDPRFilter
from market_signal_crawler.rate_limiter import DomainRateLimiter
from market_signal_crawler.database import SignalDatabase, SCHEMA_SQL
from market_signal_crawler.extractors.price_extractor import PriceExtractor
from market_signal_crawler.extractors.rss_extractor import RSSExtractor
from market_signal_crawler.extractors.metadata_extractor import MetadataExtractor
from market_signal_crawler.extractors.trend_extractor import TrendExtractor


# ============================================================================
# GDPR Filter Tests
# ============================================================================

class TestGDPRFilter(unittest.TestCase):
    """Test GDPR / PII filtering."""

    def setUp(self):
        self.strict_filter = GDPRFilter(strict=True)
        self.lenient_filter = GDPRFilter(strict=False)

    def test_email_detection(self):
        text = "Contact us at john.doe@example.com for more info"
        self.assertTrue(self.strict_filter.contains_pii(text))

    def test_phone_detection(self):
        text = "Call us at +33 1 23 45 67 89"
        self.assertTrue(self.strict_filter.contains_pii(text))

    def test_clean_text_passes(self):
        text = "Bitcoin price rose by 5% today reaching new highs"
        self.assertFalse(self.strict_filter.contains_pii(text))

    def test_strict_mode_discards(self):
        text = "Price: $100 - contact: user@email.com"
        result = self.strict_filter.filter_text(text)
        self.assertIsNone(result)

    def test_lenient_mode_redacts(self):
        text = "Price: $100 - contact: user@email.com"
        result = self.lenient_filter.filter_text(text)
        self.assertIsNotNone(result)
        self.assertIn("[REDACTED]", result)
        self.assertNotIn("user@email.com", result)

    def test_none_input(self):
        self.assertIsNone(self.strict_filter.filter_text(None))

    def test_empty_string(self):
        self.assertEqual(self.strict_filter.filter_text(""), "")

    def test_credit_card_detection(self):
        text = "Card number: 4111 1111 1111 1111"
        self.assertTrue(self.strict_filter.contains_pii(text))

    def test_iban_detection(self):
        text = "Wire to FR76 3000 6000 0112 3456 7890 189"
        self.assertTrue(self.strict_filter.contains_pii(text))

    def test_market_data_passes(self):
        text = "AAPL shares climbed 3.2% to $178.50 amid strong earnings"
        self.assertFalse(self.strict_filter.contains_pii(text))
        result = self.strict_filter.filter_text(text)
        self.assertEqual(result, text)


# ============================================================================
# Price Extractor Tests
# ============================================================================

class TestPriceExtractor(unittest.TestCase):
    """Test price signal extraction."""

    def setUp(self):
        self.extractor = PriceExtractor()

    def test_jsonld_product(self):
        html = '''<html><head>
        <script type="application/ld+json">
        {"@type": "Product", "name": "Widget X", "offers": {"price": "29.99", "priceCurrency": "USD"}}
        </script>
        </head><body></body></html>'''
        signals = self.extractor.extract("https://example.com/product", html)
        self.assertTrue(len(signals) > 0)
        self.assertEqual(signals[0]["signal_type"], "price")
        self.assertEqual(signals[0]["value"], "29.99")
        self.assertEqual(signals[0]["currency"], "USD")

    def test_opengraph_price(self):
        html = '''<html><head>
        <meta property="og:title" content="Premium Widget">
        <meta property="og:price:amount" content="49.99">
        <meta property="og:price:currency" content="EUR">
        </head><body></body></html>'''
        signals = self.extractor.extract("https://example.com/product", html)
        self.assertTrue(len(signals) > 0)
        self.assertEqual(signals[0]["currency"], "EUR")

    def test_microdata_price(self):
        html = '''<html><body>
        <div itemscope itemtype="http://schema.org/Product">
            <span itemprop="name">Gadget Y</span>
            <span itemprop="price" content="15.00">15.00</span>
            <meta itemprop="priceCurrency" content="GBP">
        </div>
        </body></html>'''
        signals = self.extractor.extract("https://example.com/gadget", html)
        self.assertTrue(len(signals) > 0)

    def test_heuristic_price(self):
        html = '<html><body><p>Current price: $123.45</p></body></html>'
        signals = self.extractor.extract("https://example.com", html)
        self.assertTrue(len(signals) > 0)
        self.assertEqual(signals[0]["extraction_method"], "heuristic")

    def test_no_prices(self):
        html = '<html><body><p>No prices here, just text.</p></body></html>'
        signals = self.extractor.extract("https://example.com", html)
        self.assertEqual(len(signals), 0)


# ============================================================================
# RSS Extractor Tests
# ============================================================================

class TestRSSExtractor(unittest.TestCase):
    """Test RSS/Atom feed parsing."""

    def setUp(self):
        self.extractor = RSSExtractor()

    def test_rss2_parsing(self):
        xml = '''<?xml version="1.0" encoding="UTF-8"?>
        <rss version="2.0">
        <channel>
            <title>Test Feed</title>
            <item>
                <title>Market Rally Continues</title>
                <link>https://example.com/article1</link>
                <description>Stocks surged today...</description>
                <pubDate>Mon, 01 Jan 2024 12:00:00 GMT</pubDate>
                <category>Markets</category>
            </item>
            <item>
                <title>Tech Sector Update</title>
                <link>https://example.com/article2</link>
                <description>Major tech companies report earnings</description>
            </item>
        </channel>
        </rss>'''
        signals = self.extractor.extract("https://example.com/feed.xml", xml)
        self.assertEqual(len(signals), 2)
        self.assertEqual(signals[0]["signal_type"], "rss_article")
        self.assertEqual(signals[0]["title"], "Market Rally Continues")
        self.assertEqual(signals[0]["categories"], "Markets")

    def test_atom_parsing(self):
        xml = '''<?xml version="1.0" encoding="UTF-8"?>
        <feed xmlns="http://www.w3.org/2005/Atom">
            <title>Atom Test Feed</title>
            <entry>
                <title>Atom Article One</title>
                <link rel="alternate" href="https://example.com/a1"/>
                <summary>Summary of article one</summary>
                <updated>2024-01-15T10:00:00Z</updated>
                <category term="Finance"/>
            </entry>
        </feed>'''
        signals = self.extractor.extract("https://example.com/atom.xml", xml)
        self.assertEqual(len(signals), 1)
        self.assertEqual(signals[0]["title"], "Atom Article One")

    def test_invalid_xml(self):
        signals = self.extractor.extract("https://example.com/bad.xml", "not xml at all <<<")
        self.assertEqual(len(signals), 0)


# ============================================================================
# Metadata Extractor Tests
# ============================================================================

class TestMetadataExtractor(unittest.TestCase):
    """Test technical metadata extraction."""

    def setUp(self):
        self.extractor = MetadataExtractor()

    def test_http_headers(self):
        html = "<html><body></body></html>"
        headers = {"server": "nginx/1.24", "x-powered-by": "Express", "content-type": "text/html"}
        signals = self.extractor.extract("https://example.com", html, headers)
        header_signal = next(s for s in signals if s["signal_type"] == "http_metadata")
        self.assertIn("nginx", header_signal["value"])

    def test_html_meta_tags(self):
        html = '''<html lang="en"><head>
        <title>Test Page</title>
        <meta name="description" content="A test description">
        <meta name="keywords" content="test, page, metadata">
        </head><body></body></html>'''
        signals = self.extractor.extract("https://example.com", html)
        meta_signal = next(s for s in signals if s["signal_type"] == "html_metadata")
        data = json.loads(meta_signal["value"])
        self.assertEqual(data["description"], "A test description")
        self.assertEqual(data["language"], "en")

    def test_technology_detection(self):
        html = '<html><body><script src="https://cdn.example.com/react.production.min.js"></script></body></html>'
        signals = self.extractor.extract("https://example.com", html)
        tech_signal = next((s for s in signals if s["signal_type"] == "technology_fingerprint"), None)
        self.assertIsNotNone(tech_signal)
        techs = json.loads(tech_signal["value"])
        self.assertIn("React", techs)

    def test_schema_types(self):
        html = '''<html><head>
        <script type="application/ld+json">{"@type": "Organization", "name": "Test"}</script>
        </head><body></body></html>'''
        signals = self.extractor.extract("https://example.com", html)
        schema_signal = next((s for s in signals if s["signal_type"] == "schema_types"), None)
        self.assertIsNotNone(schema_signal)
        types = json.loads(schema_signal["value"])
        self.assertIn("Organization", types)


# ============================================================================
# Trend Extractor Tests
# ============================================================================

class TestTrendExtractor(unittest.TestCase):
    """Test trend and sentiment extraction."""

    def setUp(self):
        self.extractor = TrendExtractor()

    def test_headline_extraction(self):
        html = '''<html><body>
        <h1>Major Market Rally Signals Recovery</h1>
        <h2>Tech Stocks Lead the Surge</h2>
        <article><h3>Crypto Markets Show Growth Patterns</h3></article>
        </body></html>'''
        signals = self.extractor.extract("https://example.com", html)
        headline_signal = next(s for s in signals if s["signal_type"] == "headlines")
        self.assertIn("Major Market Rally", headline_signal["value"])

    def test_positive_sentiment(self):
        html = '<html><body><p>Market shows growth, rally, surge, profit, and recovery.</p></body></html>'
        signals = self.extractor.extract("https://example.com", html)
        sentiment = next(s for s in signals if s["signal_type"] == "sentiment")
        self.assertGreater(float(sentiment["value"]), 0)

    def test_negative_sentiment(self):
        html = '<html><body><p>Market shows crash, decline, loss, recession, and crisis.</p></body></html>'
        signals = self.extractor.extract("https://example.com", html)
        sentiment = next(s for s in signals if s["signal_type"] == "sentiment")
        self.assertLess(float(sentiment["value"]), 0)

    def test_keyword_extraction(self):
        html = '''<html><body>
        <p>Bitcoin blockchain technology innovation. Bitcoin blockchain technology.
        Bitcoin blockchain. Cryptocurrency market analysis report.</p>
        </body></html>'''
        signals = self.extractor.extract("https://example.com", html)
        kw_signal = next((s for s in signals if s["signal_type"] == "keyword_frequency"), None)
        self.assertIsNotNone(kw_signal)
        self.assertIn("bitcoin", kw_signal["value"].lower())


# ============================================================================
# Database Tests
# ============================================================================

class TestSignalDatabase(unittest.TestCase):
    """Test SQL database operations."""

    def setUp(self):
        self.tmp = tempfile.NamedTemporaryFile(suffix=".db", delete=False)
        self.tmp.close()
        self.db = SignalDatabase(db_path=self.tmp.name)
        self.db.connect()

    def tearDown(self):
        self.db.close()
        os.unlink(self.tmp.name)

    def test_schema_creation(self):
        # Tables should exist
        tables = self.db.conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table'"
        ).fetchall()
        table_names = {row["name"] for row in tables}
        self.assertIn("market_signals", table_names)
        self.assertIn("rss_articles", table_names)
        self.assertIn("crawl_log", table_names)
        self.assertIn("crawl_sessions", table_names)

    def test_session_lifecycle(self):
        sid = self.db.start_session(config_snapshot='{"test": true}')
        self.assertIsNotNone(sid)
        self.db.end_session(sid, pages=10, signals=25)
        summary = self.db.get_session_summary(sid)
        self.assertEqual(summary["pages_crawled"], 10)
        self.assertEqual(summary["signals_stored"], 25)
        self.assertEqual(summary["status"], "completed")

    def test_store_and_retrieve_signal(self):
        sid = self.db.start_session()
        signal = {
            "source_url": "https://example.com",
            "signal_type": "price",
            "label": "Bitcoin",
            "value": "45000.00",
            "currency": "USD",
            "extraction_method": "json-ld",
            "extracted_at": datetime.now(timezone.utc).isoformat(),
        }
        self.db.store_signal(sid, signal)
        results = self.db.get_signals_by_type("price")
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0]["label"], "Bitcoin")
        self.assertEqual(results[0]["value"], "45000.00")

    def test_batch_insert(self):
        sid = self.db.start_session()
        signals = [
            {"source_url": f"https://example.com/{i}", "signal_type": "price",
             "value": str(i * 10), "extracted_at": datetime.now(timezone.utc).isoformat()}
            for i in range(5)
        ]
        count = self.db.store_signals_batch(sid, signals)
        self.assertEqual(count, 5)

    def test_rss_article_storage(self):
        sid = self.db.start_session()
        articles = [
            {"source_url": "https://feed.example.com", "title": f"Article {i}",
             "summary": "Summary", "link": f"https://example.com/{i}",
             "extracted_at": datetime.now(timezone.utc).isoformat()}
            for i in range(3)
        ]
        count = self.db.store_rss_articles_batch(sid, articles)
        self.assertEqual(count, 3)

    def test_crawl_log(self):
        sid = self.db.start_session()
        self.db.log_crawl(sid, "https://example.com", "example.com", 200, 5000, True, 3)
        self.assertTrue(self.db.is_url_crawled(sid, "https://example.com"))
        self.assertFalse(self.db.is_url_crawled(sid, "https://other.com"))

    def test_signal_count_by_type(self):
        sid = self.db.start_session()
        for t in ["price", "price", "sentiment", "headlines"]:
            self.db.store_signal(sid, {
                "source_url": "https://example.com", "signal_type": t,
                "value": "test", "extracted_at": datetime.now(timezone.utc).isoformat(),
            })
        counts = self.db.get_signal_count_by_type()
        self.assertEqual(counts["price"], 2)
        self.assertEqual(counts["sentiment"], 1)


# ============================================================================
# Rate Limiter Tests
# ============================================================================

class TestRateLimiter(unittest.TestCase):
    """Test per-domain rate limiting."""

    def test_delay_enforcement(self):
        limiter = DomainRateLimiter(default_delay=0.1)
        loop = asyncio.new_event_loop()

        start = time.time()
        loop.run_until_complete(limiter.wait("example.com"))
        loop.run_until_complete(limiter.wait("example.com"))
        elapsed = time.time() - start

        loop.close()
        # Second request should wait at least 0.1s
        self.assertGreaterEqual(elapsed, 0.08)  # small tolerance

    def test_robots_delay_override(self):
        limiter = DomainRateLimiter(default_delay=0.1)
        limiter.set_domain_delay("slow.example.com", 5.0)
        # Should use the larger value (robots.txt = 5.0)
        self.assertEqual(limiter._domain_delay["slow.example.com"], 5.0)

    def test_different_domains_independent(self):
        limiter = DomainRateLimiter(default_delay=0.5)
        loop = asyncio.new_event_loop()

        start = time.time()
        loop.run_until_complete(limiter.wait("a.com"))
        loop.run_until_complete(limiter.wait("b.com"))
        elapsed = time.time() - start

        loop.close()
        # Different domains should not block each other
        self.assertLess(elapsed, 0.4)


# ============================================================================
# Config Tests
# ============================================================================

class TestConfig(unittest.TestCase):
    """Test configuration defaults."""

    def test_defaults(self):
        config = CrawlerConfig()
        self.assertIn("MarketSignalBot", config.user_agent)
        self.assertGreater(config.default_crawl_delay, 0)
        self.assertTrue(config.gdpr_strict)
        self.assertGreater(len(config.rss_feeds), 0)
        self.assertGreater(len(config.blocked_domains), 0)

    def test_blocked_domains_include_social(self):
        config = CrawlerConfig()
        self.assertIn("facebook.com", config.blocked_domains)
        self.assertIn("linkedin.com", config.blocked_domains)


if __name__ == "__main__":
    unittest.main()
