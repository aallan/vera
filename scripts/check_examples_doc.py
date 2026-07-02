#!/usr/bin/env python
"""Extract code blocks from EXAMPLES.md and verify parseable ones still parse.

Thin wrapper over the shared parse-only doc gate in scripts/doc_annotations.py
(one gate, four documents: SKILL.md, FAQ.md, README.md, EXAMPLES.md).

Intentionally unparseable blocks carry an inline
`<!-- vera:skip-parse category="..." reason="..." -->` annotation on the
line before the fence (#538).  Annotated blocks are still parsed: one that
parses fine is a STALE annotation and fails the gate.  EXAMPLES.md currently
has no annotated blocks — all its vera blocks parse.
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
        root / "EXAMPLES.md",
        "EXAMPLES.md",
        parse_label="<examples-doc>",
        hint_category="FUTURE",
    )


if __name__ == "__main__":
    sys.exit(main())
