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
    build_skill_md,
    _version,
    _without_lastmod,
)


def sitemap_stale_reason(sitemap_path: Path, expected: str) -> str | None:
    """Return why the committed sitemap is out of date, or ``None`` if current.

    Structure-only comparison: ``<lastmod>`` dates are blanked before comparing,
    because ``build_site`` preserves them when the URL set is unchanged (so they
    no longer churn per build) but they can still legitimately differ across
    machines/days — only a change to the URL structure means the file is stale.
    """
    if not sitemap_path.exists():
        return "missing (run: python scripts/build_site.py)"
    committed = _without_lastmod(sitemap_path.read_text(encoding="utf-8"))
    if committed != _without_lastmod(expected):
        return "stale (run: python scripts/build_site.py)"
    return None


def main() -> int:
    version = _version()
    expected = {
        "llms.txt": build_llms_txt(version),
        "llms-full.txt": build_llms_full_txt(version),
        "robots.txt": build_robots_txt(),
        # sitemap.xml contains today's date, so skip exact comparison
        "index.md": build_index_md(version),
        "SKILL.md": build_skill_md(),
    }

    stale: list[str] = []
    for name, content in expected.items():
        path = DOCS / name
        if not path.exists():
            stale.append(f"  {name}: missing (run: python scripts/build_site.py)")
        elif path.read_text(encoding="utf-8") != content:
            stale.append(f"  {name}: stale (run: python scripts/build_site.py)")

    # sitemap.xml: structure-only comparison (dates are allowed to differ).
    reason = sitemap_stale_reason(DOCS / "sitemap.xml", build_sitemap_xml())
    if reason is not None:
        stale.append(f"  sitemap.xml: {reason}")

    if stale:
        print(f"ERROR: {len(stale)} site asset(s) out of date:")
        for s in stale:
            print(s)
        return 1

    print("Site assets are up-to-date.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
