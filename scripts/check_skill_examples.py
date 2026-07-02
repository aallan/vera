#!/usr/bin/env python
"""Extract code blocks from SKILL.md and verify parseable ones still parse.

Thin wrapper over the shared parse-only doc gate in scripts/doc_annotations.py
(one gate, four documents: SKILL.md, FAQ.md, README.md, EXAMPLES.md).

Blocks that are intentionally unparseable (fragments, templates, deliberately
wrong "common mistakes" examples) carry an inline annotation on the line
immediately before the fence (#538):

    <!-- vera:skip-parse category="FRAGMENT" reason="bare expression" -->

The gate still parses annotated blocks: an annotated block that parses fine
is a STALE annotation and fails the gate, so the skip surface shrinks over
time.  Malformed or dangling annotations fail the gate too.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from doc_annotations import (  # noqa: E402  (scripts/ is not a package)
    run_parse_only_gate,
)


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    return run_parse_only_gate(
        root / "SKILL.md",
        "SKILL.md",
        parse_label="<skill>",
        hint_category="FRAGMENT",
    )


if __name__ == "__main__":
    sys.exit(main())
