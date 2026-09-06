"""Stream V — #1363's demotion has to cross a module boundary (#1399).

A callee whose fact the run could neither prove nor guard is DISCLOSED, and a
caller that proves a contract only from that fact is demoted to Tier 3 with
E534.  #1373 established that within one file.  Split the very same program
across two files and the demotion vanished: an imported callee's obligations
never enter the importing run's stream, so `disclosed_fn_names` — which reads
that stream — could not see them, and the importer proved at Tier 1 from a
fact the library itself reports as neither proved nor guarded.

The fix is a per-module disclosed manifest: each module's own verification
emits its disclosed-function set, keyed by the module's owner path, and the
importer consults it through the same resolution that resolves the imported
declarations.  The cells below pin the boundary crossing at every shape the
resolution graph has — one hop, three hops, a diamond — plus the two
over-rejection controls (a clean module must NOT demote its importer) that
keep the mechanism from degenerating into "anything imported is Tier 3".

Every fixture here is a SPLIT of a single-file program whose in-module
behaviour #1373 already fixed, so each cell has a same-file twin: the two
spellings must agree, and the single-file twin is the oracle for what the
split one should say.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=600,
    )


def _tree(tmp_path: Path, files: dict[str, str]) -> dict[str, Path]:
    """Write a module tree and return name -> path."""
    tmp_path.mkdir(parents=True, exist_ok=True)
    out: dict[str, Path] = {}
    for name, text in files.items():
        p = tmp_path / f"{name}.vera"
        p.write_text(text, encoding="utf-8")
        out[name] = p
    return out


def _verify(path: Path) -> dict:
    proc = _cli("verify", "--json", str(path))
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope for {path.name} "
            f"(exit {proc.returncode})\n{proc.stdout[:400]}\n"
            f"{proc.stderr[-800:]}"
        ) from None


def _triples(result: dict) -> list[tuple[str, str, str | None]]:
    return [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ]


def _obl(result: dict, kind: str, text: str | None = None) -> dict:
    """The single obligation of *kind* (optionally whose clause reads *text*).

    Selected by the clause's own text rather than by line number: every
    fixture here is assembled from templates, so a line index would silently
    re-point at a different function the moment a template gains a line.
    """
    hits = [
        o for o in result["obligations"]
        if o["kind"] == kind
        and (text is None or o["description"] == text)
    ]
    assert len(hits) == 1, (
        f"expected exactly one {kind} obligation"
        f"{'' if text is None else f' reading {text!r}'}, got "
        f"{[(o['kind'], o['status'], o['location']['line']) for o in hits]} "
        f"out of {_triples(result)}"
    )
    return hits[0]


# ---------------------------------------------------------------------------
# Fixture sources
# ---------------------------------------------------------------------------

#: The body whose `@Nat` handler-clause binder nothing guards: `vera verify` on
#: the file that holds it reports `nat_bind` / `tier3_unguarded` / E504, which
#: is the disclosure every cell in this file is built on.
_DISCLOSING_MK = """\
{visibility} fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  int_to_nat(handle[Exn<Int>] {{
    throw(@Nat) -> {{ nat_to_int(@Nat.0) }}
  }} in {{
    throw(@Int.0)
  }})
}}
"""

#: The same signature with nothing to disclose — the over-rejection control.
_CLEAN_MK = """\
{visibility} fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  int_to_nat(@Int.0)
}}
"""

#: Reads `mk`'s `@Nat` field off a match and leans on it.  `{call}` is the
#: caller's spelling of `mk` — bare in one file, `lib::mk` across two.
_USE_IT = """\
public fn use_it(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  match {call}(@Int.0) {{
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0
  }}
}}
"""

#: The middle hop of the three-hop chain.  `Some(nat_to_int(@Nat.0))` narrows
#: an `@Int` into a GENERIC-instantiated `@Nat` constructor field, which
#: codegen does not guard — so the site is `verified` while `mk`'s fact is
#: available and `tier3_unguarded` (E504) the moment it is withheld.  That
#: flip is what makes `relay` disclosed IN TURN, and so what carries the taint
#: to a third module.
_RELAY = """\
public fn {name}(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {call}(@Int.0) {{
    Some(@Nat) -> Some(nat_to_int(@Nat.0)),
    None -> None
  }}
}}
"""

#: A call PRECONDITION in the arm body — the second consumer of the
#: sub-pattern facts, and the one that keeps a boundary-crossing disclosure
#: from being an `ensures`-only story.
_NEEDS_NONNEG = """\
{visibility} fn needs_nonneg(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{{
  @Int.0
}}
"""

_USE_PRE = """\
public fn use_pre(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {call}(@Int.0) {{
    Some(@Nat) -> needs_nonneg(nat_to_int(@Nat.0)),
    None -> 0
  }}
}}
"""


# ---------------------------------------------------------------------------
# The premise, and the same-file oracle
# ---------------------------------------------------------------------------

def test_1399_the_library_alone_discloses(tmp_path: Path) -> None:
    """`vera verify lib.vera` on its own reports the disclosure.

    The premise the whole issue rests on: the fact IS disclosed, in the
    library's own run, so an importer proving from it is proving from
    something SOME run admitted it could not establish.  If this ever stops
    holding the fixture has gone stale and every red cell below would pass
    vacuously.
    """
    paths = _tree(tmp_path, {
        "lib": _DISCLOSING_MK.format(visibility="public"),
    })
    result = _verify(paths["lib"])
    assert ("nat_bind", "tier3_unguarded", "E504") in _triples(result), (
        _triples(result)
    )


def test_1399_one_file_demotes(tmp_path: Path) -> None:
    """The oracle: in ONE file, #1373 already demotes `use_it`'s `ensures`."""
    paths = _tree(tmp_path, {
        "single": _DISCLOSING_MK.format(visibility="private")
        + "\n" + _USE_IT.format(call="mk"),
    })
    result = _verify(paths["single"])
    triples = _triples(result)
    assert ("nat_bind", "tier3_unguarded", "E504") in triples, triples
    assert ("ensures", "tier3", "E534") in triples, triples


# ---------------------------------------------------------------------------
# One hop — the issue's reproducer, verbatim
# ---------------------------------------------------------------------------

def test_1399_imported_callee_demotes_the_importer(tmp_path: Path) -> None:
    """The reproducer: the SAME program split in two must say the same thing.

    Before the fix `use_it`'s `ensures` was `verified` here and `tier3`/E534
    in the one-file spelling above — a Tier-1 proof that the file layout, and
    nothing else, produced.
    """
    paths = _tree(tmp_path, {
        "lib": _DISCLOSING_MK.format(visibility="public"),
        "main": "import lib;\n\n" + _USE_IT.format(call="lib::mk"),
    })
    result = _verify(paths["main"])
    ens = _obl(result, "ensures")
    assert (ens["status"], ens.get("error_code")) == ("tier3", "E534"), (
        f"an imported disclosed callee left the importer at Tier 1: "
        f"{_triples(result)}"
    )
    # The demotion is reported against the IMPORTING file, at the importer's
    # own contract — not against the library that made the disclosure.
    assert Path(ens["location"]["file"]).name == "main.vera", ens["location"]
    e534 = [
        w for w in result["warnings"] if w.get("error_code") == "E534"
    ]
    assert len(e534) == 1, [w.get("error_code") for w in result["warnings"]]
    assert Path(e534[0]["location"]["file"]).name == "main.vera", e534[0]
    # No obligation of the LIBRARY's leaked into the importer's stream: the
    # manifest carries the disclosed NAMES, not the module's obligations.
    assert all(
        Path(o["location"]["file"]).name == "main.vera"
        for o in result["obligations"]
    ), [o["location"] for o in result["obligations"]]


def test_1399_a_clean_module_does_not_demote_its_importer(
    tmp_path: Path,
) -> None:
    """The over-rejection control: importing is not itself a disclosure.

    Identical shape, identical import, a library with nothing disclosed — the
    importer must keep its Tier-1 proof.  Without this the demotion could be
    "every imported callee taints" and every cell above would still pass.
    """
    paths = _tree(tmp_path, {
        "lib": _CLEAN_MK.format(visibility="public"),
        "main": "import lib;\n\n" + _USE_IT.format(call="lib::mk"),
    })
    result = _verify(paths["main"])
    ens = _obl(result, "ensures")
    assert (ens["status"], ens.get("error_code")) == ("verified", None), (
        f"a clean import was demoted: {_triples(result)}"
    )


def test_1399_split_and_single_agree(tmp_path: Path) -> None:
    """Spelling-independence, stated as the equality the issue reports broken.

    The two runs' full streams differ by construction — the library's own
    obligations belong to the library's own run — so the comparison is over
    the one clause both programs contain: `use_it`'s postcondition, unique in
    each by its text.  Whatever the one-file program says about it, the split
    one has to say too; a file boundary is not a proof.
    """
    single = _verify(_tree(tmp_path / "s", {
        "single": _DISCLOSING_MK.format(visibility="private")
        + "\n" + _USE_IT.format(call="mk"),
    })["single"])
    split = _verify(_tree(tmp_path / "m", {
        "lib": _DISCLOSING_MK.format(visibility="public"),
        "main": "import lib;\n\n" + _USE_IT.format(call="lib::mk"),
    })["main"])

    def verdict(r: dict) -> tuple[str, str | None]:
        o = _obl(r, "ensures", text="@Int.result >= 0")
        return (o["status"], o.get("error_code"))

    assert verdict(single) == verdict(split), (
        f"one file says {verdict(single)}, two files say {verdict(split)}"
    )
    assert verdict(split) == ("tier3", "E534"), verdict(split)


def test_1399_selective_import_bare_call_demotes(tmp_path: Path) -> None:
    """The unqualified spelling of the same call.

    `import lib(mk);` injects `mk` into the importer's bare namespace, so the
    call reaches the verifier as a plain `FnCall` with no module path on it.
    Keying the manifest lookup off the qualified spelling alone would leave
    this one hop escaping through a syntax change.
    """
    paths = _tree(tmp_path, {
        "lib": _DISCLOSING_MK.format(visibility="public"),
        "main": "import lib(mk);\n\n" + _USE_IT.format(call="mk"),
    })
    result = _verify(paths["main"])
    ens = _obl(result, "ensures")
    assert (ens["status"], ens.get("error_code")) == ("tier3", "E534"), (
        f"a bare call to a selectively imported disclosed callee stayed at "
        f"Tier 1: {_triples(result)}"
    )


def test_1399_a_local_shadow_is_not_read_as_the_import(
    tmp_path: Path,
) -> None:
    """A local `mk` shadows the imported one, and the local one is clean.

    The bare-name route must resolve to what the call actually reaches.  A
    lookup that consulted the module manifest for any name a module happens to
    export would demote this program on the strength of a function it never
    calls.
    """
    paths = _tree(tmp_path, {
        "lib": _DISCLOSING_MK.format(visibility="public"),
        "main": "import lib(mk);\n\n"
        + _CLEAN_MK.format(visibility="private")
        + "\n" + _USE_IT.format(call="mk"),
    })
    result = _verify(paths["main"])
    ens = _obl(result, "ensures", text="@Int.result >= 0")
    assert (ens["status"], ens.get("error_code")) == ("verified", None), (
        f"a clean LOCAL callee was demoted by a same-named import: "
        f"{_triples(result)}"
    )


# ---------------------------------------------------------------------------
# The second consumer: a call precondition in the arm body
# ---------------------------------------------------------------------------

def test_1399_call_precondition_in_the_arm_demotes(tmp_path: Path) -> None:
    """`ensures` is not the only goal the withheld fact reaches.

    The arm body's call PRECONDITION reads the same sub-pattern facts, and
    with the import boundary in the way it discharged silently at Tier 1.  It
    must land where the one-file spelling lands: a `call_pre` obligation at
    `tier3` with E532.
    """
    paths = _tree(tmp_path, {
        "lib": _DISCLOSING_MK.format(visibility="public"),
        "main": "import lib;\n\n"
        + _NEEDS_NONNEG.format(visibility="private")
        + "\n" + _USE_PRE.format(call="lib::mk"),
    })
    result = _verify(paths["main"])
    triples = _triples(result)
    assert ("call_pre", "tier3", "E532") in triples, triples


def test_1399_call_precondition_control_clean_module(
    tmp_path: Path,
) -> None:
    """... and is NOT demoted when the module discloses nothing."""
    paths = _tree(tmp_path, {
        "lib": _CLEAN_MK.format(visibility="public"),
        "main": "import lib;\n\n"
        + _NEEDS_NONNEG.format(visibility="private")
        + "\n" + _USE_PRE.format(call="lib::mk"),
    })
    result = _verify(paths["main"])
    assert not [
        o for o in result["obligations"] if o["kind"] == "call_pre"
    ], _triples(result)


# ---------------------------------------------------------------------------
# Three hops — the manifest has to be transitive
# ---------------------------------------------------------------------------

_CHAIN = {
    "cb": _DISCLOSING_MK.format(visibility="public"),
    "ca": "import cb;\n\n" + _RELAY.format(name="relay", call="cb::mk"),
    "centry": "import ca;\n\n"
    + _USE_IT.format(call="ca::relay").replace("use_it", "top"),
}


def test_1399_three_hop_middle_module_is_tainted(tmp_path: Path) -> None:
    """Hop one: verifying the MIDDLE module must see the bottom one.

    `relay`'s `Some(nat_to_int(@Nat.0))` is an unguarded narrowing that the
    disclosed fact alone decides.  With `cb`'s disclosure invisible it proved
    at Tier 1; with the manifest in place it is `tier3_unguarded` + E504 —
    which is exactly what makes `relay` disclosed in `ca`'s OWN manifest.
    """
    paths = _tree(tmp_path, _CHAIN)
    result = _verify(paths["ca"])
    assert ("nat_bind", "tier3_unguarded", "E504") in _triples(result), (
        f"the middle module proved from the bottom module's disclosed fact: "
        f"{_triples(result)}"
    )


def test_1399_three_hop_entry_is_demoted(tmp_path: Path) -> None:
    """Hop two: and the entry, which never mentions `cb`, is demoted too.

    Per §8.6.4 `centry` cannot even name `cb` — the taint reaches it only
    because `ca`'s manifest was itself computed against `cb`'s.  A manifest
    that stopped at direct imports would leave this Tier 1.
    """
    paths = _tree(tmp_path, _CHAIN)
    result = _verify(paths["centry"])
    ens = _obl(result, "ensures")
    assert (ens["status"], ens.get("error_code")) == ("tier3", "E534"), (
        f"a three-hop chain stopped short: {_triples(result)}"
    )


def test_1399_three_hop_control_clean_bottom(tmp_path: Path) -> None:
    """The same chain with a clean bottom module proves at Tier 1 throughout.

    Both hops are asserted, so the cell fails if EITHER the middle module's
    narrowing or the entry's postcondition is demoted without cause.
    """
    paths = _tree(tmp_path, {
        **_CHAIN, "cb": _CLEAN_MK.format(visibility="public"),
    })
    mid = _verify(paths["ca"])
    assert ("nat_bind", "verified", None) in _triples(mid), _triples(mid)
    entry = _verify(paths["centry"])
    ens = _obl(entry, "ensures")
    assert (ens["status"], ens.get("error_code")) == ("verified", None), (
        f"a clean chain was demoted: {_triples(entry)}"
    )


# ---------------------------------------------------------------------------
# A diamond — one disclosed module, two importers, one entry
# ---------------------------------------------------------------------------

#: `da` and `db` spell their relays differently: two imports supplying one
#: bare name is E155, whatever the qualified call sites say (spec §8.5.2.2).
_DIAMOND = {
    "dc": _DISCLOSING_MK.format(visibility="public"),
    "da": "import dc;\n\n" + _RELAY.format(name="relay_a", call="dc::mk"),
    "db": "import dc;\n\n" + _RELAY.format(name="relay_b", call="dc::mk"),
    "dentry": "import da;\nimport db;\n\n"
    + _USE_IT.format(call="da::relay_a").replace("use_it", "via_a")
    + "\n"
    + _USE_IT.format(call="db::relay_b").replace("use_it", "via_b"),
}


def test_1399_diamond_both_arms_demote(tmp_path: Path) -> None:
    """Two importers of one disclosed module, joined at one entry.

    The resolver deduplicates `dc` (it is reached twice), so the manifest has
    to answer for it twice from one computation — and BOTH arms of the diamond
    must be demoted, not just whichever was resolved first.
    """
    paths = _tree(tmp_path, _DIAMOND)
    result = _verify(paths["dentry"])
    ensures = [o for o in result["obligations"] if o["kind"] == "ensures"]
    assert len(ensures) == 2, _triples(result)
    assert all(
        (o["status"], o.get("error_code")) == ("tier3", "E534")
        for o in ensures
    ), (
        f"one arm of the diamond kept its Tier-1 proof: "
        f"{[(o['status'], o.get('error_code'), o['location']['line']) for o in ensures]}"
    )


def test_1399_diamond_control_clean_base(tmp_path: Path) -> None:
    """... and neither arm is demoted when the shared base is clean."""
    paths = _tree(tmp_path, {
        **_DIAMOND, "dc": _CLEAN_MK.format(visibility="public"),
    })
    result = _verify(paths["dentry"])
    ensures = [o for o in result["obligations"] if o["kind"] == "ensures"]
    assert len(ensures) == 2, _triples(result)
    assert all(o["status"] == "verified" for o in ensures), _triples(result)


# ---------------------------------------------------------------------------
# The accounting identity survives the new status, on these programs
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "tree,entry",
    [
        pytest.param(
            {
                "lib": _DISCLOSING_MK.format(visibility="public"),
                "main": "import lib;\n\n" + _USE_IT.format(call="lib::mk"),
            },
            "main", id="one-hop",
        ),
        pytest.param(_CHAIN, "centry", id="three-hop"),
        pytest.param(_DIAMOND, "dentry", id="diamond"),
    ],
)
def test_1399_json_accounting_identity(
    tmp_path: Path, tree: dict[str, str], entry: str,
) -> None:
    """`len(obligations) == total + violated + tier3_unguarded`, per CLAUDE.md.

    The corpus leg of this identity lives in ``tests/test_obligations.py``;
    what is new here is a demotion that moves an obligation from
    ``verified`` to ``tier3`` *across a module boundary*, so the partition is
    re-asserted on exactly the programs whose statuses this change moves —
    over the ``verify --json`` envelope, which is the form a consumer reads.
    """
    paths = _tree(tmp_path, tree)
    result = _verify(paths[entry])
    v = result["verification"]
    obls = result["obligations"]
    uncounted = sum(
        1 for o in obls if o["status"] in ("violated", "tier3_unguarded")
    )
    assert v["total"] == v["tier1_verified"] + v["tier3_runtime"], v
    assert len(obls) == v["total"] + uncounted, (
        f"{len(obls)} obligations != total={v['total']} + {uncounted} "
        f"uncounted: {_triples(result)}"
    )


# ---------------------------------------------------------------------------
# The warm session must see an edit to an IMPORTED module
# ---------------------------------------------------------------------------

def _warm_ensures(
    session: object, entry: Path,
) -> tuple[str, str | None]:
    """`use_it`'s postcondition verdict from one warm re-verify of *entry*."""
    result = session.verify_source(  # type: ignore[attr-defined]
        entry.read_text(encoding="utf-8"), file=str(entry),
    )
    hits = [
        o for o in result.obligations
        if o.kind == "ensures" and o.expr_text == "@Int.result >= 0"
    ]
    assert len(hits) == 1, [
        (o.fn_name, o.kind, o.status, o.expr_text) for o in result.obligations
    ]
    # `ProofObligation.error_code` is "" when there is none; the CLI envelope
    # omits the key.  Normalise so the two spellings compare equal.
    return (hits[0].status, hits[0].error_code or None)


def test_1399_warm_session_follows_an_edit_to_the_import(
    tmp_path: Path,
) -> None:
    """Edit the LIBRARY, re-verify the ENTRY on the same warm session.

    The entry's own text never changes, so every cache key that digests only
    the entry replays — and a replayed slice carries the verdict the previous
    library produced.  Both directions are walked on ONE session, because a
    session that got the first right by starting cold would say nothing about
    the second:

    * disclosed -> clean: the demotion must LIFT.  A stale replay here is the
      annoying direction — a Tier-1 proof reported as Tier 3 forever.
    * clean -> disclosed: the demotion must APPEAR.  A stale replay here is
      the unsound one — the entry keeps claiming a proof of a fact its
      library has since stopped establishing.
    """
    from vera.obligations.session import VerificationSession

    paths = _tree(tmp_path, {
        "lib": _DISCLOSING_MK.format(visibility="public"),
        "main": "import lib;\n\n" + _USE_IT.format(call="lib::mk"),
    })
    session = VerificationSession()

    assert _warm_ensures(session, paths["main"]) == ("tier3", "E534"), (
        "the warm session did not demote in the first place"
    )

    paths["lib"].write_text(
        _CLEAN_MK.format(visibility="public"), encoding="utf-8",
    )
    assert _warm_ensures(session, paths["main"]) == ("verified", None), (
        "the library stopped disclosing and the warm session kept the "
        "demotion — a replayed slice outlived the manifest it was proved "
        "under"
    )

    paths["lib"].write_text(
        _DISCLOSING_MK.format(visibility="public"), encoding="utf-8",
    )
    assert _warm_ensures(session, paths["main"]) == ("tier3", "E534"), (
        "the library began disclosing and the warm session kept the Tier-1 "
        "proof — the unsound direction of the same staleness"
    )


def test_1399_warm_equals_cold_across_the_boundary(tmp_path: Path) -> None:
    """The warm/cold differential, on the shape the corpus does not contain.

    ``tests/test_obligations.py`` pins warm == cold over the whole corpus, and
    no corpus program has an imported disclosed callee — so the corpus leg is
    silent about exactly this change.  The generous direction is the one that
    matters: a warm session proving at Tier 1 what the cold path demotes is a
    false Tier-1 that only an editor sees.
    """
    from vera.checker import typecheck_with_artifacts
    from vera.obligations.session import VerificationSession
    from vera.parser import parse
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.verifier import verify

    paths = _tree(tmp_path, _CHAIN)
    entry = paths["centry"]
    source = entry.read_text(encoding="utf-8")

    program = transform(parse(source, file=str(entry)))
    resolver = ModuleResolver(_root=entry.parent)
    resolved = resolver.resolve_imports(program, entry)
    _diags, artifacts = typecheck_with_artifacts(
        program, source, file=str(entry), resolved_modules=resolved,
    )
    cold = verify(
        program, source, file=str(entry), resolved_modules=resolved,
        expr_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
    )
    warm = VerificationSession().verify_source(source, file=str(entry))

    def fingerprint(obligations: object) -> list[tuple[str, ...]]:
        return [
            (o.fn_name, o.kind, o.status, o.expr_text, o.error_code or "")
            for o in obligations  # type: ignore[attr-defined]
        ]

    assert fingerprint(warm.obligations) == fingerprint(cold.obligations)
    assert warm.summary == cold.summary
    assert ("top", "ensures", "tier3", "@Int.result >= 0", "E534") in \
        fingerprint(cold.obligations), fingerprint(cold.obligations)


# ---------------------------------------------------------------------------
# The other half of the key mismatch: a clone's obligations are not named
# the way a `ModuleCall` is
# ---------------------------------------------------------------------------

#: A qualified-only imported generic: `gmain` declares its own `gen`, so the
#: module's version owns no bare name here and its clones are verified under
#: the `mod$<path>$<name>` base.
_GENERIC_LIB = """\
module glib;

public forall<T> fn gen(@T, @Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  })
}
"""

_GENERIC_MAIN = """\
import glib;

private fn gen(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(@Int.0)
}

public fn use_it(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match glib::gen("x", @Int.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0
  }
}
"""


def test_1399_imported_generic_clone_is_named_by_its_module(
    tmp_path: Path,
) -> None:
    """A shadowed imported generic's clone records under `mod$<path>$<name>`.

    This is the fact that makes a bare-name lookup wrong (CR 3519156263, cited
    in #1399): the importer DOES verify this clone — its obligations are in
    this run's stream — but under a key `ModuleCall.name` does not spell.  The
    key is derived from `_module_qualified_base`, not typed as a literal, so
    the cell tracks the mangling rather than restating it.
    """
    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.verifier import ContractVerifier, verify

    paths = _tree(tmp_path, {"glib": _GENERIC_LIB, "gmain": _GENERIC_MAIN})
    entry = paths["gmain"]
    source = entry.read_text(encoding="utf-8")
    program = transform(parse(source, file=str(entry)))
    resolver = ModuleResolver(_root=entry.parent)
    resolved = resolver.resolve_imports(program, entry)
    diags, artifacts = typecheck_with_artifacts(
        program, source, file=str(entry), resolved_modules=resolved,
    )
    assert not [d for d in resolver.errors + diags if d.severity == "error"]
    result = verify(
        program, source, file=str(entry), resolved_modules=resolved,
        expr_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
    )
    clone_key = ContractVerifier._module_qualified_base(("glib",), "gen")
    names = {o.fn_name for o in result.obligations}
    assert clone_key in names, (
        f"expected the clone's obligations under {clone_key!r}, got "
        f"{sorted(names)}"
    )
    assert clone_key != "gen"


def test_1399_a_module_call_resolves_to_the_clone_key(tmp_path: Path) -> None:
    """... and the lookup answers for a call spelled the other way.

    Asserted at the method rather than through a program, deliberately.  The
    end-to-end shape cannot be built today: the demotion is driven by a match
    scrutinee's declared-type facts, and a GENERIC call does not translate to
    an SMT term, so `_subpattern_source_facts` returns before consulting
    anything (traced on the fixture above — `_scrutinee_is_disclosed_call` is
    never reached for `glib::gen(...)`).  The mismatch is therefore latent
    rather than live, and what closes it is an agreement between two spellings
    of one name, which is exactly what this checks.  Without the clone-key arm
    the lookup answers False for a call whose obligations this very run
    recorded as disclosed.
    """
    from vera import ast
    from vera.verifier import ContractVerifier

    verifier = ContractVerifier(source=_GENERIC_MAIN, file="gmain.vera")
    clone_key = ContractVerifier._module_qualified_base(("glib",), "gen")
    call = ast.ModuleCall(path=("glib",), name="gen", args=())

    verifier._disclosed_fns = frozenset()
    assert verifier._scrutinee_is_disclosed_call(call) is False

    verifier._disclosed_fns = frozenset({clone_key})
    assert verifier._scrutinee_is_disclosed_call(call) is True, (
        f"a ModuleCall named 'gen' did not resolve to {clone_key!r}, the key "
        f"its own clone's obligations are recorded under"
    )

    # ... and does not answer True for a DIFFERENT module's same-named clone.
    verifier._disclosed_fns = frozenset({
        ContractVerifier._module_qualified_base(("other",), "gen"),
    })
    assert verifier._scrutinee_is_disclosed_call(call) is False


# ---------------------------------------------------------------------------
# The manifest's own contracts: fail-closed, and computed once
# ---------------------------------------------------------------------------

def _resolved(tmp_path: Path, name: str, source: str, *, direct: bool = True):
    """A hand-built `ResolvedModule`, as a caller passing `resolved_modules`
    to `verify()` directly would supply one."""
    from vera.parser import parse
    from vera.resolver import ResolvedModule
    from vera.transform import transform

    tmp_path.mkdir(parents=True, exist_ok=True)
    path = tmp_path / f"{name}.vera"
    path.write_text(source, encoding="utf-8")
    return ResolvedModule(
        path=(name,), file_path=path,
        program=transform(parse(source, file=str(path))),
        source=source, direct=direct,
    )


def test_1399_manifest_fails_closed_on_a_module_that_will_not_check(
    tmp_path: Path,
) -> None:
    """A module nobody can verify is treated as having disclosed everything.

    The generous reading — "no obligations, so nothing was disclosed" — says
    of a module nobody managed to verify that it established all its facts,
    which is the false Tier-1 this whole mechanism exists to prevent.  The
    pipeline does not reach here (the importer's own check registers every
    resolved module's bodies, so an unclean module fails the importer's check
    first and verification never runs), but "unreachable" is not a licence to
    guess in the generous direction.
    """
    from vera.disclosure import ModuleDisclosureIndex

    mod = _resolved(tmp_path, "broken", """\
public fn one(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  "not an int"
}

public fn two(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
""")
    index = ModuleDisclosureIndex([mod], 10000)
    assert index.disclosed_in(("broken",)) == frozenset({"one", "two"})


def test_1399_manifest_of_an_unresolved_path_is_empty(tmp_path: Path) -> None:
    """A path this run never resolved supplies no name, so it discloses none.

    The complement of the fail-closed rule above, and the reason the two are
    different answers: there is no module here to have disclosed anything, and
    the name a caller would have reached through it does not resolve either.
    """
    from vera.disclosure import ModuleDisclosureIndex

    index = ModuleDisclosureIndex([], 10000)
    assert index.disclosed_in(("nowhere",)) == frozenset()


def test_1399_the_shared_base_of_a_diamond_is_verified_once(
    tmp_path: Path,
) -> None:
    """The cache is load-bearing, not a claim.

    `dc` is reached through `da` and again through `db`, by two DIFFERENT
    index objects (each arm's manifest is computed inside its own nested
    verification), so the per-index memo cannot be what deduplicates it — the
    content-addressed process cache is.  Counted rather than asserted about,
    because "cached" is exactly the kind of property that can quietly stop
    being true.
    """
    from vera import disclosure
    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.verifier import verify

    paths = _tree(tmp_path, _DIAMOND)
    entry = paths["dentry"]
    source = entry.read_text(encoding="utf-8")

    verified: list[tuple[str, ...]] = []
    original = disclosure._verify_for_disclosure

    def counting(mod, sub, timeout_ms):  # type: ignore[no-untyped-def]
        verified.append(mod.path)
        return original(mod, sub, timeout_ms)

    disclosure.clear_cache()
    disclosure._verify_for_disclosure = counting
    try:
        program = transform(parse(source, file=str(entry)))
        resolver = ModuleResolver(_root=entry.parent)
        resolved = resolver.resolve_imports(program, entry)
        _d, artifacts = typecheck_with_artifacts(
            program, source, file=str(entry), resolved_modules=resolved,
        )
        verify(
            program, source, file=str(entry), resolved_modules=resolved,
            expr_types=artifacts.expr_semantic_types,
            expr_target_types=artifacts.expr_target_types,
        )
    finally:
        disclosure._verify_for_disclosure = original

    assert verified.count(("dc",)) == 1, (
        f"the diamond's shared base was verified {verified.count(('dc',))} "
        f"times: {verified}"
    )
    assert sorted(verified) == [("da",), ("db",), ("dc",)], verified


def test_1399_the_manifest_key_tracks_every_input_it_depends_on(
    tmp_path: Path,
) -> None:
    """Same content, same key; any input changed, different key.

    A manifest is a function of the module's own source, its closure's
    sources, and the solver budget — so those three, and nothing less, have to
    be in the key.  Dropping the closure's sources is the interesting omission:
    it is the three-hop case, where a module's own text is untouched and its
    disclosed set changes anyway because something it imports began disclosing.
    """
    from vera.disclosure import ModuleDisclosureIndex

    lib = _resolved(tmp_path, "k_lib", _DISCLOSING_MK.format(
        visibility="public"))
    lib2 = _resolved(tmp_path / "b", "k_lib", _CLEAN_MK.format(
        visibility="public"))
    dep = _resolved(tmp_path, "k_dep", _CLEAN_MK.format(visibility="public"))
    dep2 = _resolved(tmp_path / "b", "k_dep", _DISCLOSING_MK.format(
        visibility="public"))

    index = ModuleDisclosureIndex([lib, dep], 10000)
    base = index._cache_key(lib, [dep])
    assert index._cache_key(lib, [dep]) == base            # deterministic
    assert index._cache_key(lib2, [dep]) != base           # own source
    assert index._cache_key(lib, [dep2]) != base           # closure source
    assert ModuleDisclosureIndex(
        [lib, dep], 20000)._cache_key(lib, [dep]) != base  # budget


def test_1399_the_manifest_cache_is_bounded(tmp_path: Path) -> None:
    """The FIFO bound, on the same reasoning as the discharge cache's.

    Keys are content-addressed, so a long-lived language-server session
    editing a library accumulates one entry per document state it verified
    under.  A real project holds a handful of live entries; the bound is the
    backstop against the session that does not stop.
    """
    from vera import disclosure

    original_max = disclosure._MAX_ENTRIES
    disclosure.clear_cache()
    disclosure._MAX_ENTRIES = 2
    try:
        for i in range(4):
            mod = _resolved(tmp_path / f"v{i}", "boundlib", f"""\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @Int.0 + {i}
}}
""")
            index = disclosure.ModuleDisclosureIndex([mod], 10000)
            assert index.disclosed_in(("boundlib",)) == frozenset()
            assert len(disclosure._CACHE) <= 2, len(disclosure._CACHE)
    finally:
        disclosure._MAX_ENTRIES = original_max
        disclosure.clear_cache()


# ---------------------------------------------------------------------------
# The sub-closure IS what the resolver would hand a standalone run
# ---------------------------------------------------------------------------

#: A tree with a transitive level under a direct import, and a diamond inside
#: it.  `otop` is where the orders can disagree: its own closure contains
#: transitive-only modules (`oc`, `od`, `oe`) reached through two paths, and
#: `od` is reachable from both arms.  Without that shape every module's
#: closure is direct-only and any traversal order looks correct.
_ORDER_TREE = {
    "oc": [],
    "od": [],
    "oe": [],
    "oa": ["oc", "od"],
    "ob": ["od", "oe"],
    "otop": ["oa", "ob"],
    "oentry": ["otop"],
}


def _order_sources() -> dict[str, str]:
    out: dict[str, str] = {}
    for name, imports in _ORDER_TREE.items():
        header = "".join(f"import {i};\n" for i in imports)
        out[name] = (header + "\n" if header else "") + f"""\
public fn {name}(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @Int.0
}}
"""
    return out


def test_1399_sub_closure_equals_what_the_resolver_hands_a_standalone_run(
    tmp_path: Path,
) -> None:
    """A DIFFERENTIAL, because the claim is a cross-component equality.

    The manifest's premise is that it says exactly what `vera verify <module>`
    says, and that only holds if the module is verified against the closure
    that command would build — same members, same `direct` flags, IN THE SAME
    ORDER.  Order is not cosmetic: several harvests over `_resolved_modules`
    are first-wins `setdefault`s (imported return types feeding generic
    discovery among them), so two orders can select different declarations.

    A hand-rolled traversal is exactly the thing that drifts from the rule it
    imitates, so this compares against `ModuleResolver` itself rather than
    against a restatement of its ordering.  Found by CodeRabbit on PR #1402: a
    LIFO stack walk emitted `otop`'s transitive-only modules as
    `od, oc, oe` where the resolver emits `oc, od, oe`.
    """
    from vera.disclosure import ModuleDisclosureIndex
    from vera.parser import parse
    from vera.resolver import ModuleResolver
    from vera.transform import transform

    paths = _tree(tmp_path, _order_sources())
    entry = paths["oentry"]
    source = entry.read_text(encoding="utf-8")
    program = transform(parse(source, file=str(entry)))
    resolver = ModuleResolver(_root=entry.parent)
    closure = resolver.resolve_imports(program, entry)
    assert not resolver.errors, resolver.errors
    assert len(closure) == len(_ORDER_TREE) - 1, [m.path for m in closure]

    index = ModuleDisclosureIndex(closure, 10000)
    for mod in closure:
        mine = [(m.path, m.direct) for m in index._sub_closure(mod)]
        standalone = ModuleResolver(_root=mod.file_path.parent)
        theirs = [
            (m.path, m.direct)
            for m in standalone.resolve_imports(mod.program, mod.file_path)
        ]
        assert mine == theirs, (
            f"{'.'.join(mod.path)}: the manifest verifies it against\n"
            f"  {mine}\n"
            f"but `vera verify` would resolve\n"
            f"  {theirs}"
        )
