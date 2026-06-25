"""Tests for ``vera.introspect`` — the registry payloads behind
``vera builtins/effects/errors --json`` (#539).

These pin the *observable* introspection contract: the schema string, the
``{schema, items}`` envelope, and — the load-bearing one — that each payload's
item count equals the live registry length, so the published counts can never
silently drift from the compiler's own tables. That drift-proofing is the whole
reason the feature exists (the doc-consolidation brief, #528).
"""

from __future__ import annotations

import pytest

from vera._since import SINCE
from vera.environment import TypeEnv
from vera.errors import ERROR_CODES
from vera.introspect import _error_phase, builtins_payload, effects_payload, errors_payload


class TestErrorsPayload:
    def test_envelope(self) -> None:
        p = errors_payload()
        assert p["schema"] == "vera-errors/1"
        assert isinstance(p["items"], list)

    def test_count_matches_registry(self) -> None:
        """The whole point of #539: the count *is* the registry's length."""
        assert len(errors_payload()["items"]) == len(ERROR_CODES)

    def test_every_registry_code_present(self) -> None:
        codes = {i["code"] for i in errors_payload()["items"]}
        assert codes == set(ERROR_CODES)

    def test_known_code_shape(self) -> None:
        by_code = {i["code"]: i for i in errors_payload()["items"]}
        e001 = by_code["E001"]
        assert e001["title"] == "Missing contract block"
        assert e001["phase"] == "parse"
        assert "since" in e001  # present even when null

    @pytest.mark.parametrize(
        ("code", "phase"),
        [
            ("W001", "warning"),
            ("E005", "parse"),
            ("E010", "parse"),
            ("E140", "typecheck"),
            ("E202", "typecheck"),
            ("E300", "typecheck"),
            ("E500", "verify"),
            ("E526", "verify"),
            ("E601", "codegen"),
            ("E700", "test"),
        ],
    )
    def test_phase_derivation(self, code: str, phase: str) -> None:
        by_code = {i["code"]: i for i in errors_payload()["items"]}
        assert by_code[code]["phase"] == phase

    def test_sorted_by_code(self) -> None:
        codes = [i["code"] for i in errors_payload()["items"]]
        assert codes == sorted(codes)

    def test_every_item_has_since_key(self) -> None:
        assert all("since" in i for i in errors_payload()["items"])

    def test_since_unattributed(self) -> None:
        # Diagnostic codes aren't version-attributed (high effort, low value) -> null.
        by_code = {i["code"]: i for i in errors_payload()["items"]}
        assert by_code["E001"]["since"] is None

    def test_error_phase_fallback(self) -> None:
        # No E4xx/E8xx codes exist today, so the registry never hits the fallback;
        # pin it directly so a refactor that drops the default is caught.
        assert _error_phase("E999") == "unknown"
        assert _error_phase("E702") == "test"


class TestBuiltinsPayload:
    def test_envelope(self) -> None:
        p = builtins_payload()
        assert p["schema"] == "vera-builtins/1"
        assert isinstance(p["items"], list)

    def test_count_matches_registry(self) -> None:
        """The published built-in count *is* the registry's length (#539)."""
        assert len(builtins_payload()["items"]) == len(TypeEnv().functions)

    def test_every_registry_name_present(self) -> None:
        names = {i["name"] for i in builtins_payload()["items"]}
        assert names == set(TypeEnv().functions)

    def test_known_builtin_shape(self) -> None:
        by_name = {i["name"]: i for i in builtins_payload()["items"]}
        sl = by_name["string_length"]
        assert sl["module"] == "core"
        assert sl["kind"] == "function"
        assert "since" in sl

    def test_sorted_by_name(self) -> None:
        names = [i["name"] for i in builtins_payload()["items"]]
        assert names == sorted(names)

    def test_every_item_has_since_key(self) -> None:
        assert all("since" in i for i in builtins_payload()["items"])

    def test_since_attribution(self) -> None:
        by_name = {i["name"]: i for i in builtins_payload()["items"]}
        assert by_name["string_length"]["since"] == "0.0.50"
        assert by_name["map_new"]["since"] == "0.0.94"
        assert by_name["decimal_add"]["since"] == "0.0.97"

    def test_since_covers_every_builtin(self) -> None:
        """Every built-in is attributed in vera/_since.py. A new built-in added
        without a `since` entry fails here — the maintenance forcing-function."""
        missing = sorted(i["name"] for i in builtins_payload()["items"] if i["since"] is None)
        assert missing == [], f"built-ins missing a `since` in vera/_since.py: {missing}"

    def test_since_no_orphan_keys(self) -> None:
        """Every SINCE key is a live registry name (error codes excepted — SINCE
        omits them) — catches an entry orphaned by a rename or removal."""
        env = TypeEnv()
        live = set(env.functions) | set(env.effects) | set(env.abilities) | {"Exn"}
        orphans = sorted(k for k in SINCE if k not in live)
        assert orphans == [], orphans


class TestEffectsPayload:
    def test_envelope(self) -> None:
        p = effects_payload()
        assert p["schema"] == "vera-effects/1"
        assert isinstance(p["items"], list)

    def test_count_registry_plus_parameterised(self) -> None:
        """The registry effects + abilities, plus the parameterised Exn<T> (#539)."""
        from vera.introspect import _PARAMETERISED_EFFECTS

        env = TypeEnv()
        expected = len(env.effects) + len(_PARAMETERISED_EFFECTS) + len(env.abilities)
        assert len(effects_payload()["items"]) == expected

    def test_parameterised_exn_effect(self) -> None:
        """Exn<T> is special-cased (codegen-recognised via handle[Exn<E>], not in
        env.effects) but surfaced for discoverability."""
        by_name = {i["name"]: i for i in effects_payload()["items"]}
        exn = by_name["Exn"]
        assert exn["kind"] == "effect"
        assert exn["type_params"] == ["T"]
        assert exn["ops"] == ["throw"]
        assert exn["since"] == "0.0.62"

    def test_io_effect_ops(self) -> None:
        by_name = {i["name"]: i for i in effects_payload()["items"]}
        io = by_name["IO"]
        assert io["kind"] == "effect"
        assert "print" in io["ops"]
        assert "read_line" in io["ops"]
        assert "since" in io

    def test_state_type_params(self) -> None:
        by_name = {i["name"]: i for i in effects_payload()["items"]}
        assert by_name["State"]["type_params"] == ["T"]

    def test_ability_kind_and_ops(self) -> None:
        by_name = {i["name"]: i for i in effects_payload()["items"]}
        eq = by_name["Eq"]
        assert eq["kind"] == "ability"
        assert eq["ops"] == ["eq"]

    def test_marker_effect_has_empty_ops(self) -> None:
        by_name = {i["name"]: i for i in effects_payload()["items"]}
        assert by_name["Async"]["ops"] == []

    def test_every_item_has_since_key(self) -> None:
        assert all("since" in i for i in effects_payload()["items"])

    def test_since_attribution(self) -> None:
        by_name = {i["name"]: i for i in effects_payload()["items"]}
        assert by_name["IO"]["since"] == "0.0.5"
        assert by_name["Random"]["since"] == "0.0.115"
        assert by_name["Eq"]["since"] == "0.0.90"

    def test_since_covers_every_effect_and_ability(self) -> None:
        missing = sorted(i["name"] for i in effects_payload()["items"] if i["since"] is None)
        assert missing == [], f"effects/abilities missing a `since`: {missing}"

    def test_names_unique(self) -> None:
        """No effect/ability is listed twice — guards the parameterised-effect
        merge against a double-listing if Exn ever enters env.effects."""
        names = [i["name"] for i in effects_payload()["items"]]
        assert len(names) == len(set(names)), names
