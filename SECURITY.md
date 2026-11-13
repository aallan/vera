# Security Policy

## Reporting a Vulnerability

If you discover a security vulnerability in Vera, please report it responsibly.

**Do not open a public issue.** Instead, use one of these channels:

1. **GitHub private vulnerability reporting** (preferred): go to the [Security tab](https://github.com/aallan/vera/security/advisories/new) and choose "Report a vulnerability". The report stays within GitHub and allows coordinated disclosure.

2. **Email**: send details to **alasdair@babilim.co.uk** if you prefer.

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

Automated security scanning runs on every push to `main` and every pull request. A pull request that changes only the VS Code extension's own files skips the dependency audit and the SBOM.

- **`ruff check --select S vera/`** (lint job): Bandit-equivalent security rules over the compiler source, for patterns such as unsafe `subprocess` use, hard-coded secrets and insecure HTTP calls. Each finding is fixed or suppressed with a `# noqa: SXXX` annotation that gives the reason.
- **`pip-audit --skip-editable`** (dependency-audit job): checks every installed package against the [OSV vulnerability database](https://osv.dev) for known CVEs. The local editable `vera` install is skipped; every third-party dependency is audited. A known unfixed CVE in a transitive dependency is suppressed with `--ignore-vuln` and a comment to revisit it when a fix ships.
- **CycloneDX SBOM** (sbom job): generates a [CycloneDX](https://cyclonedx.org) JSON Software Bill of Materials with `cyclonedx-py environment`, recording the full transitive dependency tree for each CI run. The SBOM is uploaded as a CI artifact kept for 90 days, for supply-chain auditing.
- **Gitleaks** (security job): full-history secret scanning.

### Workflow hardening

Every CI job declares least-privilege permissions, `contents: read` unless it needs more: the security job also takes `security-events: write` for GitHub advisory integration, matrix-gate `actions: read`, and matrix-issue `issues: write` to file a failed nightly cell. Every `actions/checkout` step in `ci.yml` and `release.yml` sets `persist-credentials: false`, so the `GITHUB_TOKEN` is not stored in `.git/config` for the lifetime of the runner.

Third-party GitHub Actions are pinned to major-version tags and kept current by Dependabot (`github-actions` ecosystem, `.github/dependabot.yml`). `codecov/codecov-action` is also pinned to a commit SHA, because Codecov's acquisition by Harness raises the risk that its floating tag is repointed; see [#712](https://github.com/aallan/vera/issues/712) and the CI-workarounds table in [`KNOWN_ISSUES.md`](KNOWN_ISSUES.md) for the revisit trigger.

`zizmor` reports one acknowledged `secrets-outside-env` finding: the `CODECOV_TOKEN` is passed as an action input (`token: ${{ secrets.CODECOV_TOKEN }}`) rather than through an environment variable. It cannot be fixed: `codecov/codecov-action` takes the token as an `inputs:` parameter and does not read it from an environment variable. The risk is low: the Codecov token has read-only scope on repository data, and `fail_ci_if_error: false` means missing or invalid tokens do not block CI.
