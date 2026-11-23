"""The false proof the `vera test --distrust` tests refute, injected.

`--distrust` runs the functions the verifier proved, and reports a trial
that fails a proved check as a refutation (E703).  Its tests need a program
that proves at Tier 1 and runs false, and the language has none on purpose:
each false proof the suite once held was a soundness bug, and its fix took
the fixture away.  So the false proof is injected, at the check alone.

What is injected: while the type checker runs (`vera.checker.core._check`,
the one sequence both of its entry points run), `vera.types`'
`is_formal_subtype` also admits a pair that fits once each side's
narrowings are erased (`Nat` to `Int`, a refinement to its base).  That is
the relaxation inside a function type that E190 refuses, the hole issue
1819 named: a closure declared `fn(@Int -> @Int)` passes at a
`fn(Int -> Nat)` parameter, and the `@Nat` the call returns holds -7.
`is_subtype`'s function-type rule and `unfit_function_value` both reach the
relation through that one name, so it is the one patch point; `_check` is
wrapped only to hold the patch to the check's duration.

Everything after the check is the pipeline's own, unpatched: the verifier's
Tier 1 proof that `mo(7) >= 0`, the compiled module and its checks, and the
run that refutes the proof.  `test_repro_the_false_proof_is_refused_without_the_injection`
in `tests/test_distrust_corpus.py` checks the same program with nothing
injected and asserts E190, so the day the relation changes shape and the
injection no longer admits the program, that control says so.
"""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
from typing import Any

import vera.checker.core as checker_core
import vera.types as vera_types


@contextmanager
def injected_false_proof() -> Iterator[None]:
    """Admit, at the check alone, a function value whose parameter is
    narrower or whose result is wider than the type it meets."""
    formal = vera_types.is_formal_subtype
    check = checker_core._check

    def relaxed(sub: vera_types.Type, sup: vera_types.Type) -> bool:
        return formal(sub, sup) or formal(
            vera_types._narrowing_erased(sub), vera_types._narrowing_erased(sup))

    def check_relaxed(*args: Any, **kwargs: Any) -> None:
        vera_types.is_formal_subtype = relaxed
        try:
            check(*args, **kwargs)
        finally:
            vera_types.is_formal_subtype = formal

    checker_core._check = check_relaxed
    try:
        yield
    finally:
        checker_core._check = check
