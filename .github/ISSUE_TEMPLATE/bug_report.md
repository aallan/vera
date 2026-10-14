---
name: Bug Report
about: Report a bug in the Vera compiler or tooling
title: ''
labels: bug
assignees: ''
---

## Description

A clear description of the bug.

## Mechanism, Class and Instances

Which rule produces the wrong result, and which class of input does it get wrong? Search the open `bug` issues for the mechanism first: a further sighting of an open class is a checklist line on that issue, not a new one. List the known instances as a checklist.

- [ ]

## Effect

Silent (a wrong value, a wrong proof, or a wrong program accepted, with every gate green) or loud (a failure the user sees: a compile or load error after a green check, a false refusal, a wrong message or location).

## Reach

Where a program written to accomplish something meets this shape: a file under `examples/` or `tests/conformance/`, a VeraBench task, an idiom the documentation teaches, or "none found" after looking.

## Steps to Reproduce

1. ...
2. ...

## Vera Code (if applicable)

```vera
```

## Expected Behaviour

What you expected to happen.

## Actual Behaviour

What actually happened. Include any error messages or compiler output.

## Environment

- Vera version:
- Python version:
- OS:
