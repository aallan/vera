## Summary

What does this PR do?

## Related Issues

Closes #

## Class Boundary / Class Instrument

For a bug fix: which class of inputs does this close, which mechanism bounds it, and which neighbouring inputs does it deliberately not cover, and why? Name the class instrument — the exhaustive matrix or generator that ranges over that class — and say which of its cells were red before the fix. A class whose boundary is architectural is not fixed per site: say which release removes its mechanism instead. If review reaches a fourth round, answer here which mechanism produces the members review keeps finding, and whether this PR removes it. See [CONTRIBUTING.md](../CONTRIBUTING.md) § Bugs: the class, not the instance.

## Type of Change

- [ ] Specification change
- [ ] Compiler implementation
- [ ] Bug fix
- [ ] Tests
- [ ] Documentation

## Checklist

- [ ] I have read [CONTRIBUTING.md](../CONTRIBUTING.md)
- [ ] My changes follow the project's coding standards
- [ ] I have added/updated tests as appropriate
- [ ] A bug fix closes the class its mechanism bounds, not just the reported instance, and ships a class instrument (an architectural class goes to its mechanism's release)
- [ ] I have updated relevant documentation
- [ ] All tests pass locally
