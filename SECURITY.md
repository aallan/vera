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
