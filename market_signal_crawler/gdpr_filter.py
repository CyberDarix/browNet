"""
GDPR / PII filtering module.

All extracted text passes through this filter BEFORE storage.
Any content matching personal-data patterns is redacted or discarded entirely.
"""

import re
import logging
from typing import Optional

logger = logging.getLogger("market_signal_crawler.gdpr_filter")

# --- Compiled PII detection patterns ---

# Email addresses
_EMAIL_RE = re.compile(
    r"[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}",
    re.IGNORECASE,
)

# Phone numbers (international & local formats)
_PHONE_RE = re.compile(
    r"(?:\+?\d{1,3}[\s\-]?)?"           # optional country code
    r"(?:\(?\d{1,4}\)?[\s\-]?)?"         # optional area code
    r"\d{2,4}[\s\-]?\d{2,4}[\s\-]?\d{2,4}",
)

# Social security / national ID patterns (FR, US, DE)
_SSN_RE = re.compile(
    r"\b\d{3}[\s\-]?\d{2}[\s\-]?\d{4}\b"  # US SSN
    r"|\b[12]\s?\d{2}\s?\d{2}\s?\d{2}\s?\d{3}\s?\d{3}\s?\d{2}\b"  # FR NIR
)

# Credit card numbers (basic Luhn-length patterns)
_CC_RE = re.compile(
    r"\b(?:\d{4}[\s\-]?){3}\d{4}\b"
)

# IP addresses (v4)
_IPV4_RE = re.compile(
    r"\b(?:\d{1,3}\.){3}\d{1,3}\b"
)

# Person name patterns - common "Name: ..." or "Nom : ..."
_NAME_LABEL_RE = re.compile(
    r"(?:nom|name|prenom|first\s*name|last\s*name|auteur|author|contact)"
    r"\s*[:=]\s*[A-Z\u00C0-\u017F][a-z\u00E0-\u017F]+(?:\s+[A-Z\u00C0-\u017F][a-z\u00E0-\u017F]+)+",
    re.IGNORECASE,
)

# Physical addresses (partial heuristic)
_ADDRESS_RE = re.compile(
    r"\b\d{1,5}\s+(?:rue|avenue|boulevard|street|road|av\.|blvd|st\.|rd\.)\b",
    re.IGNORECASE,
)

# IBAN
_IBAN_RE = re.compile(
    r"\b[A-Z]{2}\d{2}\s?(?:\d{4}\s?){4,7}\d{1,4}\b"
)

# All patterns grouped
_PII_PATTERNS = [
    ("email", _EMAIL_RE),
    ("phone", _PHONE_RE),
    ("ssn", _SSN_RE),
    ("credit_card", _CC_RE),
    ("ipv4", _IPV4_RE),
    ("name_label", _NAME_LABEL_RE),
    ("address", _ADDRESS_RE),
    ("iban", _IBAN_RE),
]


class GDPRFilter:
    """Filter and redact personal data from extracted text."""

    def __init__(self, strict: bool = True):
        """
        Args:
            strict: If True, discard any text block containing PII.
                    If False, redact PII in-place with [REDACTED].
        """
        self.strict = strict
        self._stats = {name: 0 for name, _ in _PII_PATTERNS}

    def contains_pii(self, text: str) -> bool:
        """Return True if the text contains any personal data patterns."""
        for name, pattern in _PII_PATTERNS:
            if pattern.search(text):
                self._stats[name] += 1
                logger.debug("PII detected (%s) in text snippet", name)
                return True
        return False

    def redact(self, text: str) -> str:
        """Replace all PII matches with [REDACTED]."""
        result = text
        for name, pattern in _PII_PATTERNS:
            result = pattern.sub("[REDACTED]", result)
        return result

    def filter_text(self, text: Optional[str]) -> Optional[str]:
        """
        Apply GDPR filtering to a text block.

        In strict mode, returns None if any PII is detected.
        In lenient mode, returns the text with PII redacted.
        """
        if not text:
            return text

        if self.strict:
            if self.contains_pii(text):
                logger.info("GDPR strict: discarding text block with PII")
                return None
            return text
        else:
            return self.redact(text)

    @property
    def stats(self):
        return dict(self._stats)
