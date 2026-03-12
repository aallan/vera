#!/usr/bin/env python
"""Verify limitation tracking is consistent across documentation tiers.

Vera documents limitations in three places:
  1. README.md — user-facing "Limitations" table
  2. vera/README.md — contributor-facing "Current Limitations" table
  3. spec/ chapters — language-design-level limitation tables (ch 8, 9, 11, 12)

This script extracts GitHub issue numbers from each tier and checks:
  - Every open limitation issue in spec or vera/README appears in README.md
  - No stale "Done" entries remain in limitation tables

With --check-states, also verifies via GitHub API that no closed issues are
listed as open limitations (slower — one API call per issue).

Fast enough for a pre-commit hook in default mode.
"""

import re
import subprocess
import sys
from pathlib import Path


def extract_limitation_table_issues(text: str, table_header: str) -> set[int]:
    """Extract issue numbers from a Markdown limitation table.

    Finds the table that follows `table_header` and extracts all issue
    references from it.  Stops at the next heading or blank line after
    the table.
    """
    issues: set[int] = set()
    in_table = False
    header_found = False

    for line in text.splitlines():
        # Look for the section heading
        if table_header in line:
            header_found = True
            continue
        if not header_found:
            continue

        # Skip blank lines between heading and table
        if not in_table and line.strip() == "":
            continue

        # Table rows start with |
        if line.strip().startswith("|"):
            in_table = True
            # Skip separator rows
            if re.match(r"^\|[\s\-|]+\|$", line.strip()):
                continue
            # Extract issue numbers from this row
            row_issues = re.findall(
                r"\[#(\d+)\]\(https://github\.com/[^)]+\)", line
            )
            issues.update(int(n) for n in row_issues)
        elif in_table:
            # Table ended
            break

    return issues


def extract_done_and_open(text: str) -> tuple[set[int], set[int]]:
    """Extract open and Done issue sets from vera/README limitation table.

    Scans all table rows in the Current Limitations section.  Rows
    containing "Done" go into the done set; others go into the open set.
    """
    open_issues: set[int] = set()
    done_issues: set[int] = set()
    in_section = False

    for line in text.splitlines():
        if "## Current Limitations" in line:
            in_section = True
            continue
        if not in_section:
            continue
        # Stop at next section
        if line.startswith("## ") and "Current Limitations" not in line:
            break
        if not line.strip().startswith("|") or "---" in line:
            continue
        row_issues = [
            int(n)
            for n in re.findall(
                r"\[#(\d+)\]\(https://github\.com/[^)]+\)", line
            )
        ]
        if "Done" in line:
            done_issues.update(row_issues)
        else:
            open_issues.update(row_issues)

    return open_issues, done_issues


def check_issue_states(issue_numbers: set[int]) -> dict[int, str]:
    """Check open/closed state of GitHub issues using gh CLI."""
    if not issue_numbers:
        return {}

    states: dict[int, str] = {}
    for num in sorted(issue_numbers):
        try:
            result = subprocess.run(
                [
                    "gh", "issue", "view", str(num),
                    "--json", "state", "-q", ".state",
                ],
                capture_output=True,
                text=True,
                timeout=10,
            )
            if result.returncode == 0:
                states[num] = result.stdout.strip()
            else:
                states[num] = "UNKNOWN"
        except (subprocess.TimeoutExpired, FileNotFoundError):
            states[num] = "UNKNOWN"

    return states


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    errors: list[str] = []

    do_check_states = "--check-states" in sys.argv

    # ------------------------------------------------------------------
    # 1. Extract limitation issues from each documentation tier
    # ------------------------------------------------------------------

    # Tier 1: README.md — user-facing limitations table
    readme_text = (root / "README.md").read_text()
    readme_issues = extract_limitation_table_issues(
        readme_text, "#### Limitations"
    )

    # Tier 2: vera/README.md — contributor-facing limitations table
    vera_readme_text = (root / "vera/README.md").read_text()
    vera_readme_open, vera_readme_done = extract_done_and_open(vera_readme_text)

    # Tier 3: Spec chapters with limitation sections
    spec_issues: dict[str, set[int]] = {}
    spec_files = [
        ("spec/08-modules.md", "## 8.11 Limitations"),
        ("spec/09-standard-library.md", "## 9.9 Limitations"),
        ("spec/11-compilation.md", "## 11.17 Limitations"),
        ("spec/12-runtime.md", "## 12.8 Limitations"),
    ]
    for spec_path, heading in spec_files:
        full_path = root / spec_path
        if full_path.exists():
            text = full_path.read_text()
            if heading.split("## ")[1] in text:
                issues = extract_limitation_table_issues(text, heading)
                if issues:
                    spec_issues[spec_path] = issues

    all_spec_issues: set[int] = set()
    for issues in spec_issues.values():
        all_spec_issues |= issues

    # ------------------------------------------------------------------
    # 2. Cross-check: every open limitation should appear in README.md
    # ------------------------------------------------------------------

    all_documented_open = vera_readme_open | all_spec_issues
    missing_from_readme = all_documented_open - readme_issues
    for num in sorted(missing_from_readme):
        sources = []
        if num in vera_readme_open:
            sources.append("vera/README.md")
        for spec_path, issues in spec_issues.items():
            if num in issues:
                sources.append(spec_path)
        errors.append(
            f"Issue #{num} appears in {', '.join(sources)} "
            f"but is missing from README.md Limitations table"
        )

    # ------------------------------------------------------------------
    # 3. Check for stale "Done" entries
    # ------------------------------------------------------------------

    if vera_readme_done:
        errors.append(
            f"vera/README.md still has {len(vera_readme_done)} 'Done' "
            f"limitation(s) that should be removed: "
            f"{', '.join(f'#{n}' for n in sorted(vera_readme_done))}"
        )

    # ------------------------------------------------------------------
    # 4. (Optional) Check for closed issues via GitHub API
    # ------------------------------------------------------------------

    if do_check_states:
        all_issues = readme_issues | vera_readme_open | all_spec_issues
        if all_issues:
            states = check_issue_states(all_issues)
            for num in sorted(all_issues):
                state = states.get(num, "UNKNOWN")
                if state == "CLOSED":
                    locations = []
                    if num in readme_issues:
                        locations.append("README.md")
                    if num in vera_readme_open:
                        locations.append("vera/README.md")
                    for spec_path, issues in spec_issues.items():
                        if num in issues:
                            locations.append(spec_path)
                    errors.append(
                        f"Issue #{num} is CLOSED but still listed as "
                        f"open limitation in: {', '.join(locations)}"
                    )

    # ------------------------------------------------------------------
    # 5. Report
    # ------------------------------------------------------------------

    if errors:
        print(
            f"ERROR: {len(errors)} limitation sync issue(s):",
            file=sys.stderr,
        )
        for err in errors:
            print(f"  {err}", file=sys.stderr)
        return 1

    mode = " (with state check)" if do_check_states else ""
    print(
        f"Limitation tracking is consistent{mode} "
        f"({len(readme_issues)} in README.md, "
        f"{len(vera_readme_open)} in vera/README.md, "
        f"{len(all_spec_issues)} across spec chapters)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
