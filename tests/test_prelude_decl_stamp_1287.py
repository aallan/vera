"""#1287: the prelude's declaration block is a fact about the prelude.

``_stamp_decl_order`` guards on ``name in self._decl_order`` before it
stamps anything.  ``_decl_order`` is the ACTIVE namespace — the main
file's, stamped from 0 in Pass 1 — so a main-file ``type Option = Int``
made the guard fire on the PRELUDE stamp in Pass 1.2, and the prelude's
own ``Option`` never entered ``_prelude_decl_order``.

That map is not a namespace.  ``_module_alias_scope`` builds every
module's index space as ``{**_prelude_decl_order, **module_own}``, so it
is the base layer UNDER every other namespace, and letting a main-file
declaration decide its contents is precisely the cross-namespace leak
``_decl_order`` and ``_module_decl_order`` were split apart to prevent
(PR #1224 review, quoted at ``vera/codegen/core.py``'s ``_decl_order``).

Two consequences, both measured here at the branch point:

1. ``Option`` is absent from the prelude block, and every prelude
   declaration AFTER it is off by one — the counter never advanced —
   so the block is a function of the main file's declarations, not of
   ``inject_prelude``'s output.
2. Inside a module's namespace the prelude ``Option`` then resolves at
   ``_BUILTIN_DECL_INDEX`` instead of its prelude position, and that
   wrong index is what reaches ``AliasEnv.data_types``, the value a
   consumer reads.

No rendering moves for these names — ``data_types`` changes an answer
only for ``Decimal`` and the single ``REMOVED_ALIASES`` entry ``Float``
(``naming._resolve_named``), and no prelude ADT is either — so, exactly
as ``test_adt_membership_scope_1253`` does for the same reason, the
assertions are on the index the consumer receives rather than on a
rendering that cannot distinguish it.

The control in every case is the SAME program without the shadowing
alias: the claim is an invariance, so the fixture states it as one.

Since #1469 the prelude's names are reserved: the shadowing alias is
refused at check (E158), so no program the check accepts reaches the guard
with a prelude name, and the cells assert the refusal beside the control's
own index.  The guard's already-stamped branch is pinned directly
(`test_the_prelude_stamp_is_idempotent_by_name`).
"""

from __future__ import annotations

from pathlib import Path

from tests import pipeline
from vera.codegen.core import _BUILTIN_DECL_INDEX, CodeGenerator

_MLIB = """
public fn tag(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""

# `Option` is a prelude ADT, and a main-file `type` of the same name was
# accepted when #1287 was found; the prelude's names are reserved since
# #1469, so the check refuses it (E158).
_SHADOWING = """
import mlib(tag);

type Option = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  tag(())
}
"""

_CONTROL = """
import mlib(tag);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  tag(())
}
"""


def _compiled(tmp_path: Path, main_src: str) -> CodeGenerator:
    """Compile *main_src* against ``mlib`` and hand back the generator.

    The compile RESULT is asserted clean before the generator is handed
    back.  Every claim below is about the bookkeeping of a program the
    compiler accepts, and discarding the result would let these cases go
    on passing over a program codegen had started refusing.
    """
    main_path = pipeline.write_tree(
        tmp_path, {"mlib.vera": _MLIB, "main.vera": main_src})
    checked = pipeline.check(main_path, root=tmp_path)
    _ = checked.program  # raises the parse or transform error
    compiled = pipeline.compile(
        main_path, modules=checked.resolved or [])
    result = compiled.result
    gen = compiled.generator
    assert gen is not None
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], [
        (d.error_code, d.description) for d in errors]
    assert result.exports == ["main"], result.exports
    return gen


def _refused(tmp_path: Path, main_src: str) -> None:
    """*main_src* is refused at check at its `type Option` (E158), so no
    stage after the check runs on it."""
    main_path = pipeline.write_tree(
        tmp_path, {"mlib.vera": _MLIB, "main.vera": main_src})
    compiled = pipeline.compile(main_path, root=tmp_path)
    errors = compiled.checked.errors
    assert [(d.error_code, d.location.line) for d in errors] == [
        ("E158", main_src.splitlines().index("type Option = Int;") + 1)
    ], [(d.error_code, d.description[:70]) for d in errors]
    assert compiled.generator is None


def test_prelude_block_does_not_depend_on_the_main_file(
    tmp_path: Path,
) -> None:
    """The same prelude injection produces the same prelude index block.

    `inject_prelude` lays down an identical declaration list for both
    programs (the shadowing one declares an ALIAS, and only a `data` of
    that name suppresses a prelude DataDecl), so the block they stamp
    must be identical too.  At the branch point the shadowing program's
    block is missing `Option` AND has every later prelude declaration
    shifted one place earlier, because the skipped stamp never advanced
    `_prelude_decl_order_next`.  The shadowing program is refused at
    check now (E158), so the block it would stamp is never built.
    """
    _refused(tmp_path / "s", _SHADOWING)
    control = _compiled(tmp_path / "c", _CONTROL)

    # The control is the oracle for what the prelude actually injected —
    # asserted, not assumed, so a prelude that stopped injecting `Option`
    # would fail here rather than make the comparison vacuous.
    assert "Option" in control._prelude_decl_order, sorted(
        control._prelude_decl_order)
    assert control._prelude_decl_order["Option"] == min(
        control._prelude_decl_order.values())


def test_module_namespace_keeps_the_prelude_index(tmp_path: Path) -> None:
    """Inside a module, the shadowed prelude ADT sits where the prelude put it.

    The index reaches consumers through `AliasEnv.data_types`, which is
    where it is asserted.  `_BUILTIN_DECL_INDEX` is the wrong answer
    twice over: it is not the prelude's position, and it is *below*
    `_PRELUDE_DECL_BASE`, so it orders the prelude's `Option` ahead of
    every other prelude declaration rather than among them.  The shadowing
    program is refused at check now (E158); the control's module namespace
    reads the prelude's own index.
    """
    _refused(tmp_path / "s", _SHADOWING)
    control = _compiled(tmp_path / "c", _CONTROL)

    with control._module_alias_scope(("mlib",)):
        expected = control._alias_env.data_types["Option"]

    assert expected != _BUILTIN_DECL_INDEX, (
        "the control reads the builtin floor inside the module namespace"
    )
    assert expected == control._prelude_decl_order["Option"], (
        expected, control._prelude_decl_order["Option"])


def test_the_prelude_stamp_is_idempotent_by_name() -> None:
    """Stamping one prelude name twice records it once, at one index.

    `_stamp_decl_order` documents itself as idempotent by name, and the
    unconditional prelude write has to keep that promise on its own now
    that it no longer borrows `_decl_order`'s guard — a second write
    would move the name AND advance the counter, shifting every prelude
    declaration after it.  Exercised directly, because the injection
    loop calls the method once per declaration and so cannot reach the
    second call; the guard is a property of the method, and this is
    where it is stated.
    """
    gen = CodeGenerator(source="", file="<test>")
    gen._stamp_decl_order("Zephyr", prelude=True)
    first = gen._prelude_decl_order["Zephyr"]
    after_one = gen._prelude_decl_order_next
    gen._stamp_decl_order("Zephyr", prelude=True)
    assert gen._prelude_decl_order["Zephyr"] == first
    assert gen._prelude_decl_order_next == after_one
    assert gen._decl_order["Zephyr"] == first
    # And a NEW name still takes the next slot, so idempotence is by name
    # rather than a counter that stopped moving.
    gen._stamp_decl_order("Nimbus", prelude=True)
    assert gen._prelude_decl_order["Nimbus"] == first + 1

    # The ALREADY-STAMPED branch, which is the one the fix turns on: a name
    # the main file stamped first must still get its own prelude index,
    # while `_decl_order` keeps the main file's.  Exercised directly rather
    # than only through the `_SHADOWING` compile, so the branch is pinned
    # even if that program stops reaching it.
    gen._stamp_decl_order("Cirrus")                    # main-file stamp
    main_index = gen._decl_order["Cirrus"]
    assert main_index >= 0, main_index
    gen._stamp_decl_order("Cirrus", prelude=True)      # prelude stamp after
    assert gen._decl_order["Cirrus"] == main_index, "the shadow lost its slot"
    assert gen._prelude_decl_order["Cirrus"] == first + 2, (
        "the prelude block skipped a name the main file had declared")


def test_a_main_file_declaration_of_a_prelude_name_is_refused(
    tmp_path: Path,
) -> None:
    """The shadow that kept the main namespace (index 0 for `type Option`,
    while the prelude block kept its own) is refused at check since #1469
    (E158), so no main-file stamp of a prelude name is ever made; the
    method's already-stamped branch keeps its direct pin above."""
    _refused(tmp_path, _SHADOWING)
