"""Show and hash dispatch on the VALUE's type, not on the compiling
namespace's reading of its name (#1534, #1539).

The WASM layer names a value's type by a string, and PR #1372 made every
decision over that string ask the namespace whose body is compiling: is the
name one of ITS data types (``_adt_type_names``), and does it declare the
name (``_declares_adt``)?  That is the right question for a name the
namespace WROTE, and the wrong one for a value's type, which is spelled
where the value was made:

* **#1534.**  A data type the entry file reaches only through an imported
  function's signature is not a member of the entry's namespace, so
  ``show`` / ``hash`` of it found no constructor plans and dropped the
  caller (E602) on a check-green program ``main`` runs.  A data type is
  named by its layout key, which has one owner after the #1317 renames,
  so the value's type identifies it whatever the namespace can name.
* **#1539.**  A namespace declaring ``data Array`` captured every array
  value's type, so ``show([1, 2])`` walked the array's ``(ptr, len)`` pair
  as a one-word ADT pointer and built a module that fails to load.  A
  type spelled with a different number of arguments than the declaration
  takes is not an instance of the declaration.

Where the two spellings take the SAME number of arguments (a built-in
``Decimal`` beside ``data Decimal``, an array beside ``data Array<T>``) the
checker gives both the one type ``AdtType(name, args)``, so the value's type
does not say which it is.  So the container names are reserved (#1547): a
``data`` declaration of ``Array``, ``Map``, ``Set`` or ``Decimal`` is
refused at check (E158), and #1539's program with it.  A prelude data
type's name stays declarable, and its same-arity cell (``UrlParts``) is a
strict xfail on #1496.

* :class:`TestTheReportedPrograms` — both issues' reproductions, at the
  output ``main`` (6dc41d40) prints.
* :class:`TestATypeReachedThroughASignature` — #1534's class: every value
  shape (an enum, a generic, a record whose field is another such type)
  at every position a show or hash reaches it through (bare, ``Some``,
  array element, tuple component, a prelude clone's result), against the
  control that imports the types too.
* :class:`TestABuiltInValueBesideADeclarationOfItsName` — #1539's class,
  over every container name code generation branches on
  (``_CONTAINER_NAMES``): refused at check whatever sits beside the
  declaration, while the control without it runs.
* :class:`TestABuiltInAdtName` — the built-in data type names the live
  registries hold: a built-in value beside a declaration of its name
  renders as in the control or is refused loudly, never as the declaration.
* :class:`TestEveryMembershipReadIsAResolver` — the instrument: every read
  of the namespace's data-type membership in ``vera/wasm`` goes through the
  two resolvers, enumerated from the code.
"""
from __future__ import annotations

import ast as pyast
from pathlib import Path

import pytest

from tests.test_check_implies_compile import pipeline, run_main
from tests.test_name_resolution_spine_1316 import _declarable_type_names
from vera.codegen.core import _CONTAINER_NAMES

_ROOT = Path(__file__).resolve().parent.parent
_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

#: The checker gives a built-in type and a same-named declaration of the same
#: arity one type, so neither the WASM layer's string nor the checker's
#: record says which a value is.  For a container name the declaration is
#: refused (#1547); a prelude data type's name is #1496's.
_CONFLATION = (
    "#1496: the checker gives a prelude data type and a same-named "
    "declaration one type")


def _fn(name: str, sig: str, body: str) -> str:
    return f"public fn {name}({sig})\n{_CONTRACT}{{\n  {body}\n}}\n"


_MB = (
    "module mb;\n\n"
    "public data Colour {\n  Red,\n  Green\n}\n\n"
    "public data Box<T> {\n  MkBox(T)\n}\n\n"
    "public data Pair {\n  MkPair(Colour, Int)\n}\n\n"
    + _fn("favourite", "@Unit -> @Colour", "Green") + "\n"
    + _fn("boxed", "@Int -> @Box<Int>", "MkBox(@Int.0)") + "\n"
    + _fn("mkpair", "@Int -> @Pair", "MkPair(Red, @Int.0)")
)


def _entry(imports: str, ret: str, body: str, decls: str = "") -> str:
    head = f"import mb({imports});\n\n" if imports else ""
    return head + decls + _fn("main", f"@Unit -> @{ret}", body)


def _run(tmp_path: Path, files: dict[str, str]) -> tuple[str, object]:
    out = pipeline(tmp_path, files)
    assert out.accepted, out.describe()
    assert out.compiles_clean, out.describe()
    return run_main(out)


def _refused(tmp_path: Path, files: dict[str, str]) -> None:
    """Refused at check with one E158, on the ``data`` line (#1547)."""
    out = pipeline(tmp_path, files)
    assert [d.error_code for d in out.check_errors] == ["E158"], (
        out.describe())
    source = files["main.vera"]
    line = source[:source.index("private data")].count("\n") + 1
    assert out.check_errors[0].location.line == line


# =====================================================================
# The reported programs
# =====================================================================


class TestTheReportedPrograms:
    """The issues' reproductions, at the output ``main`` prints."""

    @pytest.mark.parametrize("body,expected", [
        ("show(favourite(()))", "Green"),
        ("show(Some(favourite(())))", "Some(Green)"),
        ("show([favourite(())])", "[Green]"),
        ("show(Tuple(favourite(()), 1))", "(Green, 1)"),
        ("show(boxed(5))", "MkBox(5)"),
        ("show(mkpair(1))", "MkPair(Red, 1)"),
        ("show(option_unwrap_or(Some(favourite(())), favourite(())))",
         "Green"),
    ])
    def test_1534_show(self, tmp_path: Path, body: str, expected: str) -> None:
        imports = ", ".join(
            fn for fn in ("favourite", "boxed", "mkpair") if fn in body)
        assert _run(tmp_path, {
            "mb.vera": _MB, "main.vera": _entry(imports, "String", body),
        }) == ("ok", expected)

    def test_1534_hash(self, tmp_path: Path) -> None:
        """``hash`` of the imported value equals ``hash`` of the same value
        built where its type is declared."""
        got = _run(tmp_path / "v", {
            "mb.vera": _MB,
            "main.vera": _entry("favourite", "Int", "hash(favourite(()))"),
        })
        local = _run(tmp_path / "c", {"main.vera": (
            "private data Colour {\n  Red,\n  Green\n}\n\n"
            + _fn("main", "@Unit -> @Int", "hash(Green)"))})
        assert got == local and got[0] == "ok"

    @pytest.mark.parametrize("body,expected", [
        ("show([1, 2])", "[1, 2]"),
        ("show(Some([1, 2]))", "Some([1, 2])"),
        ("show([[1], [2, 3]])", "[[1], [2, 3]]"),
        ('show(["a", "b"])', "[a, b]"),
        ("show(array_range(0, 3))", "[0, 1, 2]"),
        ("show(Tuple([1, 2], 3))", "([1, 2], 3)"),
    ])
    def test_1539(self, tmp_path: Path, body: str, expected: str) -> None:
        """The program is refused at check: ``Array`` is reserved (#1547).
        Without the declaration it prints what ``main`` printed."""
        decl = "private data Array {\n  MkArr(Int)\n}\n\n"
        _refused(tmp_path / "variant", {
            "main.vera": _entry("", "String", body, decl)})
        assert _run(tmp_path / "control", {
            "main.vera": _entry("", "String", body),
        }) == ("ok", expected)


# =====================================================================
# #1534's class
# =====================================================================

#: A value whose data type the entry reaches only through ``mb``'s
#: signatures: the function that makes it, and the types that name it.
_VALUES = {
    "enum": ("favourite(())", "favourite", "Colour"),
    "generic": ("boxed(5)", "boxed", "Box"),
    "record-with-a-foreign-field": ("mkpair(1)", "mkpair", "Pair, Colour"),
}

#: Every position a show or hash reaches the value through.
_POSITIONS = {
    "bare": "{v}",
    "option": "Some({v})",
    "array-element": "[{v}]",
    "tuple-component": "Tuple({v}, 1)",
    "prelude-clone-result": "option_unwrap_or(Some({v}), {v})",
}

_OPS = {"show": "String", "hash": "Int"}

#: A generic clone's result is named by the generic's bare head (#772), so
#: `show` of a `Box<Int>` that `option_unwrap_or` returns has lost its
#: argument and is refused (E602) whether or not the entry imports `Box`:
#: on main and the release branch alike, and so outside this class
#: (#1550).
_EXCLUDED = frozenset({("generic", "prelude-clone-result")})


def _signature_cells() -> list[object]:
    return [
        pytest.param(value, position, op, id=f"{value}-{position}-{op}")
        for value in sorted(_VALUES) for position in sorted(_POSITIONS)
        for op in sorted(_OPS) if (value, position) not in _EXCLUDED
    ]


class TestATypeReachedThroughASignature:
    """#1534: importing the TYPE too must not change what show or hash does.

    The control imports the value's types beside the function, so the entry
    namespace holds them; the variant imports the function alone.  Both must
    compile clean and return the same value.
    """

    @pytest.mark.parametrize("value,position,op", _signature_cells())
    def test_same_as_importing_the_type(
        self, tmp_path: Path, value: str, position: str, op: str,
    ) -> None:
        expr, fn, types = _VALUES[value]
        body = f"{op}({_POSITIONS[position].format(v=expr)})"
        variant = _run(tmp_path / "variant", {
            "mb.vera": _MB, "main.vera": _entry(fn, _OPS[op], body)})
        control = _run(tmp_path / "control", {
            "mb.vera": _MB,
            "main.vera": _entry(f"{fn}, {types}", _OPS[op], body)})
        assert control[0] == "ok", control
        assert variant == control

    @pytest.mark.parametrize("op", sorted(_OPS))
    @pytest.mark.parametrize("value", sorted(_VALUES))
    def test_inside_a_closure_body(
        self, tmp_path: Path, value: str, op: str,
    ) -> None:
        """A closure's body is compiled on its own path
        (``vera/codegen/closures.py``), which must hand the dispatch the
        same value types: ``show`` or ``hash`` of the value inside a lambda,
        mapped over two elements and joined (PR #1508 review)."""
        expr, fn, types = _VALUES[value]
        # The hash is rendered in the lambda rather than carried out of it:
        # a hash above `i64.MAX` traps where it is bound into a `Nat` slot.
        shown = f"show({expr})" if op == "show" else f"show(hash({expr}))"
        body = (
            "array_fold(array_map([1, 2], fn(@Int -> @String) "
            f"effects(pure) {{ {shown} }}), \"\", "
            "fn(@String, @String -> @String) effects(pure) "
            "{ string_concat(@String.1, @String.0) })")
        variant = _run(tmp_path / "variant", {
            "mb.vera": _MB, "main.vera": _entry(fn, "String", body)})
        control = _run(tmp_path / "control", {
            "mb.vera": _MB,
            "main.vera": _entry(f"{fn}, {types}", "String", body)})
        assert control[0] == "ok", control
        assert variant == control

    def test_a_constructor_name_the_entry_reuses(
        self, tmp_path: Path,
    ) -> None:
        """The entry's own ``MkDuo`` places its parameters the other way
        round.  The index table the render reads is the ENTRY's projection,
        so it answers for ``mb``'s ``MkDuo`` only if it asks whose
        constructor the name is; read unasked, it lays ``Duo<Int, String>``
        out as ``(Int, String)`` where ``MkDuo(Y, X)`` stores
        ``(String, Int)``."""
        mb = (
            "module mb;\n\n"
            "public data Duo<X, Y> {\n  MkDuo(Y, X)\n}\n\n"
            + _fn("duo", "@Int -> @Duo<Int, String>", 'MkDuo("s", @Int.0)'))
        decl = "private data Local<A, B> {\n  MkDuo(A, B)\n}\n\n"
        assert _run(tmp_path, {
            "mb.vera": mb,
            "main.vera": _entry("duo", "String", "show(duo(5))", decl),
        }) == ("ok", "MkDuo(s, 5)")

    @pytest.mark.parametrize("op", sorted(_OPS))
    def test_a_field_of_an_imported_type(
        self, tmp_path: Path, op: str,
    ) -> None:
        """The entry imports ``Pair`` and ``MkPair`` but not the ``Colour``
        in its field, which the render reaches only through the layout."""
        body = f"{op}(MkPair(favourite(()), 1))"
        variant = _run(tmp_path / "variant", {
            "mb.vera": _MB,
            "main.vera": _entry("Pair, MkPair, favourite", _OPS[op], body)})
        control = _run(tmp_path / "control", {
            "mb.vera": _MB,
            "main.vera": _entry("Pair, MkPair, favourite, Colour",
                                _OPS[op], body)})
        assert control[0] == "ok", control
        assert variant == control


# =====================================================================
# #1539's class
# =====================================================================

#: A built-in value of each container, and a show / hash / measure of it.
#: Keyed by EVERY name in `_CONTAINER_NAMES`, which the completeness cell
#: below holds this table to.
_CONTAINER_VALUES: dict[str, tuple[tuple[str, str], ...]] = {
    "Array": (
        ("String", "show([1, 2])"),
        ("Int", "hash([1, 2])"),
        ("String", "show(Some([1, 2]))"),
        ("Int", "hash(Some([1, 2]))"),
        ("String", "show([[1], [2, 3]])"),
        ("String", "show(Tuple([1, 2], 3))"),
        ("Int", "array_length([[1], [2, 3]])"),
        ("Int", "array_length(option_unwrap_or(Some([1, 2]), []))"),
    ),
    "Map": (
        ("Int", "map_size(map_insert(map_new(), 1, 2))"),
        ("Int", "array_length([map_new(), map_insert(map_new(), 1, 2)])"),
    ),
    "Set": (
        ("Int", "set_size(set_add(set_new(), 1))"),
        ("Int", "array_length([set_new(), set_add(set_new(), 1)])"),
    ),
    "Decimal": (
        ("String", "show(decimal_from_int(5))"),
    ),
}

_SHADOW = "private data {N} {{\n  MkShadow(Int)\n}}\n\n"


def _container_cells() -> list[object]:
    return [
        pytest.param(name, ret, body, id=f"{name}|{body}")
        for name in sorted(_CONTAINER_VALUES)
        for ret, body in _CONTAINER_VALUES[name]
    ]


class TestABuiltInValueBesideADeclarationOfItsName:
    """#1539's class, at check: a declaration named like a container is
    refused (E158, #1547), whatever sits beside it, and the same program
    without the declaration runs.

    Before the reservation the variant compiled, and matched the control
    only where the declaration took a different number of type arguments
    from the container: beside ``data Decimal`` the value rendered as the
    declaration, and beside ``data Array<T>`` the module failed to load.
    """

    def test_every_container_has_values(self) -> None:
        assert set(_CONTAINER_VALUES) == set(_CONTAINER_NAMES)

    @pytest.mark.parametrize("name,ret,body", _container_cells())
    def test_refused_beside_the_value(
        self, tmp_path: Path, name: str, ret: str, body: str,
    ) -> None:
        control = _run(tmp_path / "control", {
            "main.vera": _entry("", ret, body)})
        assert control[0] == "ok", control
        _refused(tmp_path / "variant", {
            "main.vera": _entry("", ret, body, _SHADOW.format(N=name))})

    @pytest.mark.parametrize("name", sorted(_CONTAINER_NAMES))
    @pytest.mark.parametrize("body", [
        "show(MkShadow(3))", "show([MkShadow(3)])", "show(Some(MkShadow(3)))",
    ])
    def test_refused_beside_its_own_values(
        self, tmp_path: Path, name: str, body: str,
    ) -> None:
        """The declaration's own values do not make it legal."""
        _refused(tmp_path, {
            "main.vera": _entry("", "String", body, _SHADOW.format(N=name))})

    def test_a_generic_declaration_of_the_same_arity(
        self, tmp_path: Path,
    ) -> None:
        """#1547's second program: ``main`` printed ``[1, 2]``, and the
        release branch built a module that fails to load."""
        decl = "private data Array<T> {\n  MkArr(T)\n}\n\n"
        _refused(tmp_path, {
            "main.vera": _entry("", "String", "show([1, 2])", decl)})


# =====================================================================
# The built-in data type names
# =====================================================================

#: A shown built-in value of each built-in data type name.  A name with no
#: entry says why in `_NO_SHOWN_VALUE`; the completeness cell holds the two
#: to every declarable name the live registries hold that is not a container.
_ADT_VALUES = {
    "Option": "show(Some(1))",
    "Ordering": "show(compare(1, 2))",
    "Result": 'show(url_parse("http://a.b/c"))',
    "UrlParts": 'show(url_parse("http://a.b/c"))',
}
#: A built-in data type whose instances take as many arguments as the
#: declaration below, so the value renders by the declaration's layout,
#: on main and the release branch alike.  A prelude data type's name is not
#: reserved, so this stays a strict xfail on #1496.
_SAME_ARITY_ADTS = frozenset({"UrlParts"})
_NO_SHOWN_VALUE = {
    "Json": "show refuses a Json value in any program (E602)",
    "HtmlNode": "show refuses an HtmlNode value in any program (E602)",
    "MdBlock": "show refuses an MdBlock value in any program (E602)",
    "MdInline": "show refuses an MdInline value in any program (E602)",
    "Request": "no built-in makes a Request outside `vera serve`",
    "Response": "no built-in makes a Response outside `vera serve`",
}


class TestABuiltInAdtName:
    """A declaration named like a built-in data type takes that name's
    layout slot, so the built-in value has no layout left to render by:
    it renders as in the control, or the program is refused loudly (E6xx).
    It never renders as the declaration, and never builds a module that
    fails to load."""

    def test_every_name_is_accounted_for(self) -> None:
        names = set(_declarable_type_names()) - set(_CONTAINER_NAMES)
        assert set(_ADT_VALUES) | set(_NO_SHOWN_VALUE) == names
        assert not set(_ADT_VALUES) & set(_NO_SHOWN_VALUE)

    @pytest.mark.parametrize("name", [
        pytest.param(name, marks=[pytest.mark.xfail(
            strict=True, reason=_CONFLATION)] if name in _SAME_ARITY_ADTS
            else [])
        for name in sorted(_ADT_VALUES)
    ])
    def test_right_or_refused(self, tmp_path: Path, name: str) -> None:
        body = _ADT_VALUES[name]
        control = _run(tmp_path / "control", {
            "main.vera": _entry("", "String", body)})
        assert control[0] == "ok", control
        out = pipeline(tmp_path / "variant", {
            "main.vera": _entry("", "String", body, _SHADOW.format(N=name))})
        if not out.accepted:
            return
        if not out.compiles_clean:
            assert any((d.error_code or "").startswith("E6")
                       for d in out.drops), out.describe()
            return
        assert run_main(out) == control


# =====================================================================
# The instrument
# =====================================================================

#: The two resolvers: the only functions in `vera/wasm` that read the
#: compiling namespace's data-type membership, or the compilation's
#: owner-unique data types, directly.
_RESOLVERS = frozenset({"_declares_adt", "_value_adt_key"})
_MEMBERSHIP = frozenset({"_adt_type_names", "_value_data_types"})


def _membership_readers_in(source: str, file: str) -> dict[str, list[int]]:
    """Every function in *source* reading either membership set, with the
    lines it reads them on: a class's methods, keyed ``file:Class.fn``, and
    a module-level function, keyed ``file:<module>.fn``."""
    out: dict[str, list[int]] = {}
    tree = pyast.parse(source)
    owned: list[tuple[str, pyast.FunctionDef | pyast.AsyncFunctionDef]] = [
        ("<module>", fn) for fn in tree.body
        if isinstance(fn, (pyast.FunctionDef, pyast.AsyncFunctionDef))]
    for node in pyast.walk(tree):
        if isinstance(node, pyast.ClassDef):
            owned += [
                (node.name, fn) for fn in node.body
                if isinstance(fn, (pyast.FunctionDef, pyast.AsyncFunctionDef))]
    for owner, fn in owned:
        lines = [
            n.lineno for n in pyast.walk(fn)
            if isinstance(n, pyast.Attribute) and n.attr in _MEMBERSHIP
        ]
        if lines and fn.name != "__init__":
            out[f"{file}:{owner}.{fn.name}"] = lines
    return out


def _membership_readers() -> dict[str, list[int]]:
    """Every function in ``vera/wasm`` reading either membership set,
    with the lines it reads them on, from the source."""
    out: dict[str, list[int]] = {}
    for path in sorted((_ROOT / "vera" / "wasm").glob("*.py")):
        out.update(_membership_readers_in(
            path.read_text(encoding="utf-8"), path.name))
    return out


class TestEveryMembershipReadIsAResolver:
    """Every question a WASM decision asks of the namespace's data types
    goes through ``_declares_adt`` (arity-aware) or ``_value_adt_key``
    (the value's type, by layout key), so no decision reads a bare head
    against the membership again."""

    def test_only_the_resolvers_read_the_membership(self) -> None:
        readers = _membership_readers()
        assert {k.rsplit(".", 1)[1] for k in readers} == _RESOLVERS, readers

    def test_the_scan_sees_a_raw_read(self) -> None:
        """The scan is live: it reports the resolvers themselves."""
        readers = _membership_readers()
        assert any(k.endswith("._declares_adt") for k in readers)
        assert any(k.endswith("._value_adt_key") for k in readers)

    def test_the_scan_sees_a_module_level_function(self) -> None:
        """A read outside any class is reported too, so a helper function in
        ``vera/wasm`` cannot read the membership unseen."""
        source = ("def helper(ctx):\n    return ctx._adt_type_names\n\n"
                  "class C:\n    def m(self):\n"
                  "        return self._value_data_types\n")
        assert _membership_readers_in(source, "x.py") == {
            "x.py:<module>.helper": [2], "x.py:C.m": [6]}
