#!/usr/bin/env python3
"""Verify that docs/ site assets are up-to-date with source documentation.

Regenerates all site assets in memory and compares against the committed
files.  Exits non-zero if any file is stale, printing which ones need
rebuilding.

Usage:
    python scripts/check_site_assets.py

Fix stale assets by running:
    python scripts/build_site.py
"""

from __future__ import annotations

import sys
from pathlib import Path

# Add project root to path so we can import the build script
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from build_site import (  # noqa: E402
    DOCS,
    build_index_md,
    build_llms_full_txt,
    build_llms_txt,
    build_robots_txt,
    build_sitemap_xml,
    _version,
)


def main() -> int:
    version = _version()
    expected = {
        "llms.txt": build_llms_txt(version),
        "llms-full.txt": build_llms_full_txt(version),
        "robots.txt": build_robots_txt(),
        # sitemap.xml contains today's date, so skip exact comparison
        "index.md": build_index_md(version),
    }

    stale: list[str] = []
    for name, content in expected.items():
        path = DOCS / name
        if not path.exists():
            stale.append(f"  {name}: missing (run: python scripts/build_site.py)")
        elif path.read_text() != content:
            stale.append(f"  {name}: stale (run: python scripts/build_site.py)")

    # For sitemap.xml, just check it exists (date changes daily)
    if not (DOCS / "sitemap.xml").exists():
        stale.append("  sitemap.xml: missing (run: python scripts/build_site.py)")

    if stale:
        print(f"ERROR: {len(stale)} site asset(s) out of date:")
        for s in stale:
            print(s)
        return 1

    print("Site assets are up-to-date.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
