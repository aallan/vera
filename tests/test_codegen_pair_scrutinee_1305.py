"""#1305 — a `match` whose SCRUTINEE has the (ptr, len) pair representation.

``_translate_match`` saved the scrutinee into ONE local allocated at the
inferred WAT type.  A ``String`` or ``Array<T>`` scrutinee infers
``"i32_pair"`` — the two-word pseudo-type, not a WAT value type — so the
emitted module carried ``(local $l1 i32_pair)`` and never assembled:

    WAT compilation failed: unexpected token, expected one of: `i32`, ...
         --> <anon>:588:16
          |
      588 |     (local $l2 i32_pair)

The issue reached this through ``json_keys``, and framed it as an
``Option<Array<String>>`` payload binder.  Measured at the branch point,
that framing does not hold and the defect is wider:

* ``json_keys`` returns ``Array<String>``, not ``Option<Array<String>>``
  (``vera/environment.py`` ``functions["json_keys"]``, and the prelude body
  in ``vera/prelude.py``), so its result was never a match BINDER problem —
  ``array_length(json_keys(j))`` compiled and ran at the branch point.
* The trigger is the scrutinee's representation, nothing to do with JSON or
  with ``Array<String>``: ``match @String.0 { @String -> ... }`` and
  ``match @Array<Int>.0 { @Array<Int> -> ... }`` — both legal, check-green,
  single-binding matches — emitted the same invalid local.

The issue's own repro additionally matches ``Some``/``None`` against an
``Array<String>``.  A pair type has no constructors and no tag, so codegen
cannot lower that; it now raises a LOUD skip naming the situation instead
of emitting a tag read over the array's first four bytes.  (The checker
accepting that program at all is a separate hole, #1315, outside this fix.)
"""
from __future__ import annotations

import re

import pytest

from vera.codegen import execute

from tests.codegen_helpers import _compile, _compile_ok, _run, wat_fn_body


_PAIR_LOCAL_RE = re.compile(r"\(local \$\w+ i32_pair\)")


def _run_value(source: str, fn: str, args: list[object] | None = None) -> object:
    result = _compile_ok(source)
    return execute(result, fn_name=fn, args=args).value


def _assert_assembles(source: str) -> str:
    """Compile, assert the module assembled, and return its WAT."""
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"did not assemble: {[d.description for d in errors]}"
    assert not _PAIR_LOCAL_RE.search(result.wat), (
        "emitted an i32_pair local: "
        f"{_PAIR_LOCAL_RE.findall(result.wat)}"
    )
    return result.wat


class TestLegalPairScrutinee:
    """The honest core of the bug: well-typed matches on a pair scrutinee."""

    def test_match_binding_on_a_string_scrutinee(self) -> None:
        """Base: ``(local $l2 i32_pair)``; the module never assembled."""
        source = """\
public fn f(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @String.0 {
    @String -> string_length(@String.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f("abcd")
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 4

    def test_match_binding_on_an_array_scrutinee(self) -> None:
        source = """\
public fn f(@Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Array<Int>.0 {
    @Array<Int> -> array_length(@Array<Int>.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([1, 2, 3])
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 3

    def test_the_bound_string_keeps_its_bytes(self) -> None:
        """Both halves must survive the bind, not just the pointer.

        A fix that allocated two locals but copied only the pointer would
        still pass a length-free assertion; returning the bound value makes
        the length load-bearing.
        """
        source = """\
public fn f(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @String.0 {
    @String -> string_concat(@String.0, "!")
  }
}

public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  f("hi")
}
"""
        assert _run_value(source, fn="main") == "hi!"

    def test_match_on_a_string_returning_call_scrutinee(self) -> None:
        """A pair-typed CALL result, not a slot — the same local allocation."""
        source = """\
public fn f(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match string_upper(@String.0) {
    @String -> string_length(@String.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f("abc")
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 3

    def test_match_on_an_array_returning_builtin_scrutinee(self) -> None:
        source = """\
public fn f(@Map<String, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match map_keys(@Map<String, Int>.0) {
    @Array<String> -> array_length(@Array<String>.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(map_insert(map_insert(map_new(), "a", 1), "b", 2))
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 2


def _assert_refused(source: str, arm: str, entry: str = "main") -> None:
    """The match arm *arm* is refused by a LOCATED skip, and nothing runs.

    Three assertions, because the failure modes they catch are different
    and a subset of them passes on a broken compiler:

    * the module still assembles (no ``i32_pair`` local, no WAT failure) —
      the #1305 symptom;
    * a diagnostic names the pair representation AT the offending arm's own
      line — a skip located on the enclosing function would read as if the
      whole body were unsupported;
    * the entry point does not survive, so no value can be returned.  This
      is the one that separates a refusal from the silent answer: without
      it, the ``true ->`` arms below still export a ``main`` that returns
      100 from a heap pointer read as a truth value.
    """
    result = _compile(source)
    assert not _PAIR_LOCAL_RE.search(result.wat), (
        f"emitted an i32_pair local: {_PAIR_LOCAL_RE.findall(result.wat)}")
    wat_failures = [
        d for d in result.diagnostics if "WAT compilation failed" in d.description
    ]
    assert not wat_failures, (
        f"module does not assemble: {[d.description[:120] for d in wat_failures]}")

    want_line = next(
        i for i, ln in enumerate(source.splitlines(), 1) if arm in ln)
    located = [
        d for d in result.diagnostics
        if "(ptr, len) pair" in d.description
        and d.location is not None and d.location.line == want_line
    ]
    assert located, (
        f"expected a pair-representation skip located at line {want_line} "
        f"({arm!r}); got "
        f"{[(d.location.line if d.location else None, d.description[:90]) for d in result.diagnostics]}"
    )
    assert entry not in result.exports, (
        f"{entry!r} survived the refusal and is still exported "
        f"(exports={result.exports}) — the arm was lowered, not refused"
    )


# Every pattern kind that is NOT a wildcard or a binding, over both pair
# spellings.  Each entry: (id, scrutinee type, argument, the arm text).
_UNLOWERABLE_ARMS: list[tuple[str, str, str, str]] = [
    ("string-bool", "@String", '"q"', "true -> 100,"),
    ("string-int", "@String", '"q"', "1 -> 100,"),
    ("array-bool", "@Array<Int>", "[1, 2]", "true -> 100,"),
    ("array-int", "@Array<Int>", "[1, 2]", "1 -> 100,"),
    ("string-string", "@String", '"q"', '"yes" -> 100,'),
]


class TestPairScrutineeGuardIsAWhitelist:
    """Only a wildcard or a binding pattern lowers over a pair scrutinee.

    The first cut of this guard was a BLACKLIST — it named
    ``ConstructorPattern`` and ``NullaryPattern`` — and a pair has no
    comparable scalar word either, so the literal patterns fell straight
    through it into the arm-condition emitter.  That was strictly worse
    than the bug being fixed: at the branch point ``match @String.0 { true
    -> 100, _ -> 200 }`` was a loud WAT failure, and under the blacklist it
    became **check-green, exit 0, printing 100** — the scrutinee's heap
    pointer used as the truthiness condition.  The ``1 ->`` twin was the
    late-failure variant: ``vera compile`` exited 0 and shipped a ``.wasm``
    that died at instantiation with no diagnostic and no E-code.

    So the guard is a whitelist, and these cells are what makes it one.
    """

    @pytest.mark.parametrize(
        "scrutinee,arg,arm", [c[1:] for c in _UNLOWERABLE_ARMS],
        ids=[c[0] for c in _UNLOWERABLE_ARMS],
    )
    def test_unlowerable_arm_is_refused(
        self, scrutinee: str, arg: str, arm: str,
    ) -> None:
        source = f"""\
private fn probe({scrutinee} -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  match {scrutinee}.0 {{
    {arm}
    _ -> 200
  }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  probe({arg})
}}
"""
        _assert_refused(source, arm)


class TestIssueRepro:
    """The issue's programs: no invalid WAT, and a located refusal.

    ``Some``/``None`` over an ``Array<String>`` is not a lowerable match —
    a pair has no tag word.  What must not happen is what happened at the
    branch point: an ``i32_pair`` local that stops the whole module from
    assembling, taking every other function with it.
    """

    _KEY_COUNT = ("Some(@Array<String>) -> array_length(@Array<String>.0),", """\
public fn key_count(@Json -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_keys(@Json.0) {
    Some(@Array<String>) -> array_length(@Array<String>.0),
    None -> 0
  }
}
""")

    _KEY_BLOB = ("Some(@Array<String>) -> string_join(@Array<String>.0, \",\"),", """\
public fn key_blob(@Json -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_keys(@Json.0) {
    Some(@Array<String>) -> string_join(@Array<String>.0, ","),
    None -> ""
  }
}
""")

    # The nullary arm FIRST.  Both programs above lead with ``Some``, so the
    # loop hit a ConstructorPattern before it ever reached the ``None``, and
    # the NullaryPattern half of the guard was droppable green.  This cell
    # is the one that kills that mutation.
    _NULLARY_FIRST = ("None -> 0,", """\
public fn key_count(@Json -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_keys(@Json.0) {
    None -> 0,
    Some(@Array<String>) -> array_length(@Array<String>.0)
  }
}
""")

    @pytest.mark.parametrize(
        "arm,source",
        [_KEY_COUNT, _KEY_BLOB, _NULLARY_FIRST],
        ids=["array_length", "string_join", "nullary_arm_first"],
    )
    def test_module_assembles_and_the_skip_is_located(
        self, arm: str, source: str,
    ) -> None:
        entry = "key_blob" if "key_blob" in source else "key_count"
        _assert_refused(source, arm, entry=entry)


def _push_pattern(local: str = r"\d+") -> re.Pattern[str]:
    """The full ``gc_shadow_push`` idiom — push AND shadow-pointer advance.

    Same shape ``test_codegen_gc_rooting.py`` pins: without the advance
    every later push overwrites one slot, so both halves are matched in
    order.
    """
    return re.compile(
        r"global\.get \$gc_sp\s+"
        rf"local\.get ({local})\s+"
        r"i32\.store\s+"
        r"global\.get \$gc_sp\s+"
        r"i32\.const 4\s+"
        r"i32\.add\s+"
        r"global\.set \$gc_sp",
        re.MULTILINE,
    )


_SET_RE = re.compile(r"^\s*local\.set (\d+)\s*$")
_GET_RE = re.compile(r"^\s*local\.get (\d+)\s*$")


def _pair_locals(wat_body: str) -> set[tuple[int, int]]:
    """Every ``(ptr_local, len_local)`` pair the emitted body reveals.

    Two idioms carry a pair, and both are read rather than assumed:

    * the STACK-POP save — ``local.set L`` then ``local.set P`` on adjacent
      lines.  A pair is pushed pointer-first, so the length pops first and
      the SECOND ``local.set`` is the pointer;
    * the COPY — ``local.get X; local.set P; local.get X+1; local.set L``,
      which is how a binding takes its own two locals from the scrutinee's
      consecutive pair.

    Deriving the roles from the instruction order is what makes the rooting
    assertion independent of local NUMBERING, which is what the weaker
    version of that test was accidentally relying on.
    """
    lines = wat_body.splitlines()
    pairs: set[tuple[int, int]] = set()
    for i in range(len(lines) - 1):
        first, second = _SET_RE.match(lines[i]), _SET_RE.match(lines[i + 1])
        if first and second:
            pairs.add((int(second.group(1)), int(first.group(1))))
    for i in range(len(lines) - 3):
        g1, s1 = _GET_RE.match(lines[i]), _SET_RE.match(lines[i + 1])
        g2, s2 = _GET_RE.match(lines[i + 2]), _SET_RE.match(lines[i + 3])
        if g1 and s1 and g2 and s2 and int(g2.group(1)) == int(g1.group(1)) + 1:
            pairs.add((int(s1.group(1)), int(s2.group(1))))
    return pairs


class TestPairScrutineeRooting:
    """A pair scrutinee adds NO shadow roots — as EMISSION (#1322).

    Both pushes this class originally pinned are gone.  They rooted an
    ADDRESS the producer had already rooted (a parameter in the prologue, an
    allocation at its ``$alloc``, a call's result in the callee's epilogue):
    the scrutinee copy, and then the binder's copy of that copy.  The shadow
    stack roots addresses, not locals, so the duplicates bought the mark
    phase nothing while costing two slots for the whole frame — three roots
    per frame took a ``String``-scrutinee recursion to a bare `unreachable`
    at depth 1 364 (#1322).

    That the pushes were never load-bearing was already on the record here:
    deleting both left the whole suite, the GC rooting and reclamation
    suites, and four hostile allocate-inside-the-arm probes green under
    ``VERA_EAGER_GC=1``.  What makes deleting them SAFE rather than merely
    untested is ``_scope_match_shadow_roots``: its ``$gc_sp`` snapshot is
    taken before the scrutinee, so the producer's root is reclaimed only
    once the arm is done with it.

    Still a WAT assertion rather than a behavioural one, for the same reason
    as before — no probe distinguishes the emissions at run time.  The
    direction of the pin is what changed: the delta against the match-free
    twin must now be ZERO, so re-adding either duplicate goes red.
    """

    _SOURCE = """\
public fn f(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @String.0 {
    @String -> string_length(string_concat(@String.0, "z"))
  }
}
"""

    # The same body with the match removed.  Everything else — the parameter
    # prologue's own rooting, the `string_concat` intermediates — is
    # identical, so the DIFFERENCE is exactly what the match contributes.
    _CONTROL = """\
public fn f(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(string_concat(@String.0, "z"))
}
"""

    def test_the_match_adds_no_pushes_over_the_no_match_control(
        self,
    ) -> None:
        """A differential, not an absolute count.

        An absolute number would pin whatever the surrounding lowering
        happens to root as well and would move for reasons that have
        nothing to do with a match.  The delta against the match-free twin
        isolates the scrutinee copy and the binder copy — the two roots
        #1322 removed — and goes red if either is re-added.
        """
        matched = _push_pattern().findall(
            wat_fn_body(_compile_ok(self._SOURCE).wat, "f"))
        control = _push_pattern().findall(
            wat_fn_body(_compile_ok(self._CONTROL).wat, "f"))
        # An equality between two counts is satisfied by 0 == 0, so a
        # pattern that stopped matching the emitted push shape would turn
        # this into a green test that pins nothing.  Both bodies DO push —
        # the parameter prologue's root and the `string_concat`
        # intermediates — so requiring a match is a property of the
        # programs, not of the fix.
        assert control, (
            "_push_pattern matched no push in a body that allocates: the "
            "pattern has drifted from the emitted `gc_shadow_push` shape "
            "and the delta below would hold vacuously"
        )
        assert len(matched) == len(control), (
            f"match body has {len(matched)} shadow pushes (locals {matched}), "
            f"match-free control has {len(control)} (locals {control}); "
            f"a pair scrutinee and its binder are copies of an address the "
            f"producer already rooted, so the match must add none"
        )

    def test_the_pushed_local_is_the_pointer_half_not_the_length(self) -> None:
        """Position, from the pairs the WAT itself declares.

        The first version of this test inferred "is a length" from local
        NUMBERING — no pushed local may be another's successor — and that
        does not check its own name: rooting the length at both of the
        (since removed, #1322) match sites pushed ``{0, 3, 5, 10}``, where
        no element is another's successor, so the wrong half passed while
        the delta stayed 2.  The rule it enforces still binds every push
        the body does make: the parameter prologue's and the
        ``string_concat`` intermediates'.

        So recover the pairs instead of guessing them.  A (ptr, len) pair is
        visible in the emitted code as one of exactly two idioms — the
        stack-pop save, where the length pops first because the pointer was
        pushed first, and the copy, where consecutive source locals are read
        in order — and each recovered pair then answers the question
        directly: whichever half is rooted must be the pointer.
        """
        wat = wat_fn_body(_compile_ok(self._SOURCE).wat, "f")
        pushed = {int(m) for m in _push_pattern().findall(wat)}
        pairs = _pair_locals(wat)
        assert pairs, f"recovered no (ptr, len) pairs from:\n{wat}"

        rooted_wrong = [(p, ln) for p, ln in pairs if ln in pushed]
        assert not rooted_wrong, (
            f"a LENGTH half is shadow-rooted: pairs {sorted(rooted_wrong)} "
            f"have their length in pushed={sorted(pushed)}.  Only the "
            f"pointer half is a heap reference; rooting the length roots a "
            f"byte count and leaves the buffer unrooted."
        )
        assert pushed, (
            "no shadow pushes at all in this body: the assertion above "
            "would hold vacuously, so it no longer checks its own name"
        )


class TestControlsThatAlreadyCompiled:
    """The issue's two compiling controls, kept as regression guards."""

    def test_map_keys_used_directly(self) -> None:
        source = """\
public fn n(@Map<String, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(map_keys(@Map<String, Int>.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  n(map_insert(map_new(), "a", 1))
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 1

    def test_json_keys_used_directly(self) -> None:
        """``json_keys``'s result was usable at the branch point, and stays so."""
        source = """\
public fn key_count(@Json -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(json_keys(@Json.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_parse("{\\"a\\": 1, \\"b\\": 2}") {
    Ok(@Json) -> key_count(@Json.0),
    Err(@String) -> 0 - 1
  }
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 2

    def test_json_get_array_some_binder(self) -> None:
        source = """\
public fn n(@Json -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_get_array(@Json.0, "xs") {
    Some(@Array<Json>) -> array_length(@Array<Json>.0),
    None -> 0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_parse("{\\"xs\\": [1, 2, 3]}") {
    Ok(@Json) -> n(@Json.0),
    Err(@String) -> 0 - 1
  }
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 3


# (payload spelling, the expression that builds one, the fold over the
# binder, the expected value)
_PAYLOADS: list[tuple[str, str, str, int]] = [
    ("Array<String>", "map_keys(map_insert(map_new(), \"a\", 1))",
     "array_length(@Array<String>.0)", 1),
    ("Array<Int>", "[4, 5, 6, 7]", "array_length(@Array<Int>.0)", 4),
    ("Map<String, Int>", "map_insert(map_new(), \"k\", 9)",
     "map_size(@Map<String, Int>.0)", 1),
    ("Set<String>", "set_add(set_new(), \"s\")", "set_size(@Set<String>.0)", 1),
    ("String", "\"abcde\"", "string_length(@String.0)", 5),
    ("Int", "11", "@Int.0", 11),
]


class TestOptionAndResultBinderBattery:
    """Match binders over ``Option`` / ``Result`` payloads of every shape.

    The scrutinee here is a genuine ADT pointer, so these were green at the
    branch point — they are the boundary of the fix, proving the pair-typed
    SCRUTINEE change left pair-typed constructor FIELDS alone.
    """

    @pytest.mark.parametrize(
        "payload,build,fold,expected", _PAYLOADS,
        ids=[p[0] for p in _PAYLOADS],
    )
    def test_option_payload(
        self, payload: str, build: str, fold: str, expected: int,
    ) -> None:
        source = f"""\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match Some({build}) {{
    Some(@{payload}) -> {fold},
    None -> 0 - 1
  }}
}}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == expected

    @pytest.mark.parametrize(
        "payload,build,fold,expected", _PAYLOADS,
        ids=[p[0] for p in _PAYLOADS],
    )
    def test_result_payload(
        self, payload: str, build: str, fold: str, expected: int,
    ) -> None:
        source = f"""\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match Ok({build}) {{
    Ok(@{payload}) -> {fold},
    Err(@String) -> 0 - 1
  }}
}}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == expected

    def test_array_of_json_payload(self) -> None:
        source = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_parse("{\\"xs\\": [1, 2]}") {
    Ok(@Json) -> match json_get_array(@Json.0, "xs") {
      Some(@Array<Json>) -> array_length(@Array<Json>.0),
      None -> 0 - 1
    },
    Err(@String) -> 0 - 2
  }
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 2

    def test_nested_option_of_array_of_string(self) -> None:
        source = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(Some(map_keys(map_insert(map_new(), "a", 1)))) {
    Some(@Option<Array<String>>) -> match @Option<Array<String>>.0 {
      Some(@Array<String>) -> array_length(@Array<String>.0),
      None -> 0 - 1
    },
    None -> 0 - 2
  }
}
"""
        _assert_assembles(source)
        assert _run(source, fn="main") == 1
