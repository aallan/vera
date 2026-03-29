# Security Policy

## Reporting a Vulnerability

If you discover a security vulnerability in Vera, please report it responsibly.

**Do not open a public issue.** Instead, use one of these channels:

1. **GitHub private vulnerability reporting** (preferred) — go to the [Security tab](https://github.com/aallan/vera/security/advisories/new) and click "Report a vulnerability". This keeps the report within GitHub and allows coordinated disclosure.

2. **Email** — send details to **alasdair@babilim.co.uk** if you prefer.

In either case, include:

- A description of the vulnerability
- Steps to reproduce
- Any relevant Vera code or compiler output

You should receive a response within 72 hours. We will work with you to understand the issue and coordinate a fix before any public disclosure.

## Scope

Security issues in the following areas are in scope:

- The reference compiler (arbitrary code execution, path traversal, etc.)
- The WASM runtime sandbox (escape, capability leaks)
- The verification system (unsound verification, false proofs)

Issues in the language specification that affect soundness of the type system or contract system are also relevant and can be reported via the same channel.

## CI Security Practices

The project uses automated security scanning on every push and pull request:

- **`ruff check --select S vera/`** (lint job) — Bandit-equivalent security rules applied to the compiler source. Detects patterns such as unsafe `subprocess` use, hardcoded secrets, and insecure HTTP calls. All findings are reviewed and either fixed or explicitly suppressed with a `# noqa: SXXX` annotation explaining why.
- **`pip-audit --skip-editable`** (dependency-audit job) — Scans all installed packages against the [OSV vulnerability database](https://osv.dev) for known CVEs. The local editable `vera` install is skipped (it is not on PyPI); all third-party dependencies are audited. Known unfixed CVEs in transitive dependencies are suppressed with `--ignore-vuln` and a comment to revisit when a fix ships.
- **CycloneDX SBOM** (sbom job) — Generates a [CycloneDX](https://cyclonedx.org) JSON Software Bill of Materials via `cyclonedx-py environment`, capturing the full transitive dependency tree at the point of each CI run. The SBOM is uploaded as a 90-day CI artifact for supply-chain auditing.
- **Gitleaks** (security job) — Full-history secret scanning on every push and PR.

### Workflow hardening

All CI jobs use least-privilege permissions (`permissions: contents: read`). The security job additionally requires `security-events: write` for GitHub advisory integration. All `actions/checkout` steps set `persist-credentials: false` to prevent the `GITHUB_TOKEN` from being stored in `.git/config` for the lifetime of the runner.

Action version pinning to SHA hashes (rather than semver tags) is tracked in [#390](https://github.com/aallan/vera/issues/390).
