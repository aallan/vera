"""Mixin for function compilability checks.

Determines whether a function can be compiled to WASM based on its
effects, parameter types, and return type.  Also scans function bodies
for State handler expressions.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence

from vera import ast
from vera.narrowing import COMPILABLE_EFFECTS, MEMORY_EFFECTS
from vera.monomorphize import mangle_type_name
from vera.wasm.helpers import CellNames
from vera.wasm.async_fusion import await_needs_check, fused_async_target

MAX_CELL_FAMILY_SYMBOL = 4096
"""Longest mangled State/Exn cell family symbol the compiler will emit.

A State cell family becomes the module AND field string of four WASM
imports, and the binary format caps a single name string at 100,000
bytes -- wasmparser rejects the module with ``string size out of
bounds`` before any host sees it.  Nothing bounded the family, so a
refinement predicate could produce one past that: check, verify and
compile all passed and ``vera run`` then failed to PARSE the module the
compiler had just emitted, while the browser host -- which reads the
same bytes through a different parser -- ran it (PR #1238 review).

Since #1238 the family renders through ``vera fmt``'s canonical
expression form, so its length is LINEAR in the predicate a user wrote:
the reviewer's 44-conjunct shape mangles to 1,578 characters, against
112,626 under the newline-indented tree it replaced.  This is the
backstop for the residue, not the fix.

Why 4,096 and not the hard limit.  The binding constraint is on the
FIELD string, ``state_get_`` plus the symbol, so ~99,990 is what the
format actually permits.  Refusing two dozen times earlier is deliberate:

* the compiler's own diagnostic should be what a user meets, not a
  host's parse error, and only a margin makes that true across the
  encoder, the three runtimes, and whatever a future one adds;
* the symbol appears about a dozen times in the emitted text (four
  imports, each a module/field pair, plus the identifiers and every call
  site), so the cap bounds the WAT roughly a dozen times over.

The measured band this can fire in is narrow and entirely pathological.
100 left-nested conjuncts mangle to 3,594 and pass; 200 reach 7,294 and
are refused; the PARSER itself recursion-errors around 500, so nothing
beyond ~400 arrives here at all.  No predicate a person writes is close.
"""

UNSUPPORTED_CELL_TYPE = ""
"""The refusal reason meaning "this type has no cell at all".

The registration methods return a reason string rather than a bool so the
caller's diagnostic can say WHICH refusal happened; this empty one selects
the long-standing E607/E612 wording, and a non-empty one replaces it.  A
sentinel rather than ``None`` because ``None`` already means "registered".
"""


def _oversized_family_reason(family: str) -> str | None:
    """The refusal reason for a family whose symbol is past the cap.

    ``None`` when it fits.  Measured on the MANGLED form, because that is
    what reaches the name string — the canonical family is shorter, and
    checking it would let an escape-heavy predicate through.  See
    :data:`MAX_CELL_FAMILY_SYMBOL` for why this exists and why 4,096.
    """
    n = len(mangle_type_name(family))
    if n <= MAX_CELL_FAMILY_SYMBOL:
        return None
    return (
        f"a cell family symbol of {n:,} characters, past the "
        f"{MAX_CELL_FAMILY_SYMBOL:,}-character limit"
    )


def contract_exprs(
    contracts: Sequence[ast.Contract],
) -> Iterator[ast.Expr]:
    """Every predicate expression carried by a function's contracts.

    One enumeration shared by both import pre-scans (#1210 round 2), because
    a contract is LOWERED code: `requires` / `ensures` become runtime checks
    and `decreases` becomes the termination guard's measure, so anything in
    one that needs a host import or a State/Exn family needs it registered.

    `Decreases` is why this exists at all: it carries `exprs` (a tuple — a
    lexicographic measure is several expressions) where the other kinds carry
    `expr`, so the `getattr(c, "expr")` shortcut this replaced silently
    skipped it and a `handle[State<Nat>]` in a `decreases` measure emitted
    `state_push_Nat` against an import that was never declared.

    The dispatch is EXPLICIT rather than attribute-probing (round-5 review).
    A `getattr` fallback treats an unrecognised contract kind as "carries
    nothing", which is the silent-skip failure this function was written to
    fix — and it hides the field accesses from mypy, so a renamed field would
    typecheck.  A new `ast.Contract` subclass now raises here instead, at the
    commit that adds it.
    """
    for contract in contracts:
        if isinstance(contract, (ast.Requires, ast.Ensures, ast.Invariant)):
            yield contract.expr
        elif isinstance(contract, ast.Decreases):
            yield from contract.exprs
        else:
            raise TypeError(
                f"contract_exprs does not know how to enumerate the "
                f"predicates of {type(contract).__name__} — a new "
                f"ast.Contract subclass must be added here (and to the "
                f"walkers' WALKER_COVERAGE checklists), or its expressions "
                f"go unregistered while codegen lowers them"
            )


class CompilabilityMixin:
    """Methods for checking if functions are compilable to WASM."""

    def _scan_anon_fn_signature(
        self, node: ast.AnonFn, scan: Callable[[ast.Node], None],
    ) -> None:
        """Walk the boundary-guard predicates of a closure's SIGNATURE (#1210
        round 7), shared by both pre-scan walkers.

        The walkers descend an `AnonFn`'s BODY because the closure compile
        pipeline runs no scan of its own on lifted bodies.  Its SIGNATURE is
        lowered there too: `closures.py` emits a runtime guard for every
        refined formal and for a refined return, so `fn(@Big -> @Int)` behind
        an `apply_fn` — with `Big` a refinement whose predicate contains a
        `handle[State<Nat>]` — emitted `state_push_Nat` against an import
        nothing declared.  `_signature_refinement_predicates` is the ONE
        derivation of what those guards check; this walks what it yields.

        Cycle-guarded, because a refinement predicate may contain a closure
        whose own formal is refined by the same alias: `type R = { @Int | …
        fn(@R -> @Int) … }` type-checks, and expanding R's predicate reaches
        that closure, whose signature expands R's predicate again.  The stack
        is popped on the way out, so this suppresses only genuine re-entry —
        a later function meeting the same closure still gets its own
        registration verdict (and, for the handler walk, its own E607/E612).
        """
        if id(node) in self._anon_sig_scan_stack:
            return
        self._anon_sig_scan_stack.add(id(node))
        try:
            for pred in self._signature_refinement_predicates(node):
                scan(pred)
        finally:
            self._anon_sig_scan_stack.discard(id(node))

    def _is_compilable(self, decl: ast.FnDecl) -> bool:
        """Check if a function can be compiled to WASM.

        Accepts pure functions, IO effects, and State<T> where T is
        a compilable primitive type (Int, Nat, Bool, Float64).
        """
        # Check effect: must be pure, <IO>, or <State<T>>
        effect = decl.effect
        if isinstance(effect, ast.PureEffect):
            pass  # OK
        elif isinstance(effect, ast.EffectSet):
            for eff in effect.effects:
                if isinstance(eff, ast.EffectRef):
                    # #754: membership is ONE test against the shared roster,
                    # not the tail of a per-effect chain.  The verifier reads
                    # the same roster to decide whether an operation argument
                    # can be guarded at all — an operation of an effect this
                    # rejects has no run to guard — and a chain whose accepted
                    # names were listed only by its own branches gave that
                    # question no table to consult.
                    if eff.name not in COMPILABLE_EFFECTS:
                        self._warning(
                            decl,
                            f"Function '{decl.name}' uses unsupported "
                            f"effect '{eff.name}' — skipped.",
                            rationale=(
                                "Only pure and the built-in effects are "
                                "compilable: "
                                + ", ".join(sorted(COMPILABLE_EFFECTS))
                                + "."
                            ),
                            error_code="E603",
                        )
                        return False
                    if eff.name == "State":
                        # State<T> — T must be a compilable primitive
                        if not self._check_state_type(decl, eff):
                            return False
                    elif eff.name == "Exn":
                        # Exn<E> — E must be a compilable type
                        if not self._check_exn_type(decl, eff):
                            return False
                    elif eff.name in MEMORY_EFFECTS:
                        # IO / Http / HttpServer (#305, the marker effect
                        # whose accept loop lives in the `vera serve` driver)
                        # / Inference / DB (#229, whose ops read
                        # Option<String> params and return row grids on the
                        # heap) all touch linear memory.  `Async` (sequential
                        # execution) and `Random` (#465) need no host memory.
                        self._needs_memory = True
                else:
                    return False
        else:
            return False

        # Check parameter types
        for p in decl.params:
            wt = self._type_expr_to_wasm_type(p)
            if wt == "unsupported":
                self._warning(
                    decl,
                    f"Function '{decl.name}' has unsupported parameter type "
                    f"— skipped.",
                    rationale=(
                        "WASM code generation supports a fixed set of "
                        "parameter types; this parameter's type is not among "
                        "them, so the function is skipped rather than "
                        "miscompiled."
                    ),
                    error_code="E604",
                )
                return False

        # Check return type
        ret_wt = self._type_expr_to_wasm_type(decl.return_type)
        if ret_wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' has unsupported return type "
                f"— skipped.",
                rationale=(
                    "WASM code generation supports a fixed set of return "
                    "types; this function's return type is not among them, "
                    "so the function is skipped rather than miscompiled."
                ),
                error_code="E605",
            )
            return False

        return True

    def _check_state_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Validate a State<T> effect and register its type.

        Returns True if compilable, False otherwise.
        """
        if not eff.type_args or len(eff.type_args) != 1:
            self._warning(
                decl,
                f"Function '{decl.name}' uses State without "
                f"a type argument — skipped.",
                rationale="State<T> requires exactly one type argument.",
                error_code="E606",
            )
            return False
        type_arg = eff.type_args[0]
        reason = self._register_state_cell(type_arg)
        if reason is not None:
            self._warn_unsupported_state_cell(decl, decl.name, reason)
            return False
        return True

    def _register_state_cell(
        self, type_arg: ast.TypeExpr,
    ) -> str | None:
        """Register the `State<type_arg>` host-cell family; False if it has none.

        The ONE place a State cell's compilability is decided and its family
        recorded, shared by the declared-effect gate (`_check_state_type`)
        and the handler walk (`_scan_expr_for_handlers`) — the two paths must
        accept exactly the same cell types, or a handler discharging the
        effect inside a `pure` function registers nothing while its lowering
        emits the calls anyway (#1210: `handle[State<String>]` was
        check-green invalid WASM).

        The import FAMILY is the cell the CHECKER typed (#1209), so every
        alias spelling that resolves to it — scalar (#1205), composite,
        parameterised — registers ONE family.  `wt` is derived from the
        RESOLVED type, so registering an unresolved name split the family
        (`state_put_Count` typed i64) from the name the per-function lowering
        derives; resolving both keeps them one.
        """
        wt = self._type_expr_to_wasm_type(type_arg)
        if wt is None or wt in ("unsupported", "i32_pair"):
            return UNSUPPORTED_CELL_TYPE
        cell = CellNames(
            family=self._family_name_te(type_arg),
            base=self._family_base_te(type_arg),
        )
        oversized = _oversized_family_reason(cell.family)
        if oversized is not None:
            return oversized
        if cell.family and (cell, wt) not in self._state_types:
            self._state_types.append((cell, wt))
        return None

    def _warn_unsupported_state_cell(
        self, node: ast.Node, fn_name: str,
        reason: str = UNSUPPORTED_CELL_TYPE,
    ) -> None:
        """The E607 both State-cell paths emit — one wording, one code.

        *reason* selects between the two refusals `_register_state_cell`
        can make: the empty :data:`UNSUPPORTED_CELL_TYPE` is the cell type
        with no WASM representation, and a non-empty one is the oversized
        family symbol (#1238 review), which needs to name the length and
        the cap or the user cannot tell what to shorten.
        """
        if reason:
            self._warning(
                node,
                f"Function '{fn_name}' uses State with {reason} — skipped.",
                rationale=(
                    "A State<T> cell family becomes the module and field "
                    "string of its four WASM imports, and the binary format "
                    "caps a name string at 100,000 bytes; the compiler "
                    f"refuses past {MAX_CELL_FAMILY_SYMBOL:,} characters so "
                    "the module is never emitted in a form a host cannot "
                    "load.  A refined cell type carries its predicate into "
                    "the family, so the length is the predicate's: "
                    "shorten it, or move the condition into the "
                    "function's contracts and leave the cell type "
                    "unrefined."
                ),
                error_code="E607",
            )
            return
        self._warning(
            node,
            f"Function '{fn_name}' uses State with "
            "unsupported type — skipped.",
            rationale="State<T> requires a compilable primitive type "
            "(Int, Nat, Bool, Float64).",
            error_code="E607",
        )

    def _check_exn_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Validate an Exn<E> effect and register its type.

        Returns True if compilable, False otherwise.
        """
        if not eff.type_args or len(eff.type_args) != 1:
            self._warning(
                decl,
                f"Function '{decl.name}' uses Exn without "
                f"a type argument — skipped.",
                rationale="Exn<E> requires exactly one type argument.",
                error_code="E611",
            )
            return False
        type_arg = eff.type_args[0]
        reason = self._register_exn_tag(type_arg)
        if reason is not None:
            self._warn_unsupported_exn_tag(decl, decl.name, reason)
            return False
        return True

    def _warn_unsupported_exn_tag(
        self, node: ast.Node, fn_name: str,
        reason: str = UNSUPPORTED_CELL_TYPE,
    ) -> None:
        """The E612 both Exn-tag paths emit — one wording, one code.

        The `_warn_unsupported_state_cell` twin.  Both registration paths
        (the declared-effect gate and the handler walk) must reach the same
        verdict on the same payload type, or a handler discharging `Exn<E>`
        inside a `pure` function registers no tag while its lowering emits
        `throw $exn_E` / `catch $exn_E` regardless — `unknown tag $exn_Unit`
        at whole-module WAT compilation, from a check-green program (#1210).

        *reason* selects between the two refusals exactly as the State twin
        does.  The oversized-family one applies here for symmetry rather
        than for the same hazard: a tag name is a WAT-text identifier that
        the encoder resolves to an index, so it never becomes a name string
        and cannot cross the 100,000-byte cap.  Refusing both keeps ONE
        answer to "is this family emittable?" — the two registration paths
        already have to agree (#1210), and a rule that held for State and
        not for Exn is the shape of that bug.
        """
        if reason:
            self._warning(
                node,
                f"Function '{fn_name}' uses Exn with {reason} — skipped.",
                rationale=(
                    "An Exn<E> tag family and a State<T> cell family are "
                    "emitted from one derivation and refused by one rule; "
                    f"past {MAX_CELL_FAMILY_SYMBOL:,} characters the family "
                    "is not emitted.  A refined payload type carries its "
                    "predicate into the family, so the length is the "
                    "predicate's: shorten it, or move the condition into "
                    "the function's contracts and leave the payload type "
                    "unrefined."
                ),
                error_code="E612",
            )
            return
        self._warning(
            node,
            f"Function '{fn_name}' uses Exn with "
            f"unsupported type — skipped.",
            rationale="Exn<E> requires a compilable type "
            "(Int, Nat, Bool, Float64, String).",
            error_code="E612",
        )

    def _register_exn_tag(self, type_arg: ast.TypeExpr) -> str | None:
        """Register the `Exn<type_arg>` WASM tag; False if it has none.

        The State twin (`_register_state_cell`): one derivation shared by the
        declared-effect gate and the handler walk, so a tag reached only from
        a handler nested in a clause body is declared rather than emitted
        undeclared (#1210).

        The tag FAMILY resolves exactly like the State import family —
        `Exn<Code>` with `type Code = Int` otherwise declares an i64 tag the
        i32-typed catch sites of the unresolved-name derivation cannot match,
        and `Exn<Payload>` with `type Payload = Option<Int>` declares a
        second tag beside the `Option<Int>` one its throw sites target
        (#1209).  Unlike a State cell, an `i32_pair` payload IS compilable:
        the tag takes two i32 params.
        """
        wt = self._type_expr_to_wasm_type(type_arg)
        if wt is None or wt == "unsupported":
            return UNSUPPORTED_CELL_TYPE
        wasm_tag_t = "i32 i32" if wt == "i32_pair" else wt
        type_name = self._family_name_te(type_arg)
        oversized = _oversized_family_reason(type_name)
        if oversized is not None:
            return oversized
        if type_name and (type_name, wasm_tag_t) not in self._exn_types:
            self._exn_types.append((type_name, wasm_tag_t))
        return None

    _MD_BUILTINS = frozenset({
        "md_parse", "md_render", "md_has_heading",
        "md_has_code_block", "md_extract_code_blocks",
    })

    _REGEX_BUILTINS = frozenset({
        "regex_match", "regex_find", "regex_find_all", "regex_replace",
    })

    _MAP_BUILTINS = frozenset({
        "map_new", "map_insert", "map_get", "map_contains",
        "map_remove", "map_size", "map_keys", "map_values",
    })

    _SET_BUILTINS = frozenset({
        "set_new", "set_add", "set_contains",
        "set_remove", "set_size", "set_to_array",
    })

    _DECIMAL_BUILTINS = frozenset({
        "decimal_from_int", "decimal_from_float", "decimal_from_string",
        "decimal_to_string", "decimal_to_float",
        "decimal_add", "decimal_sub", "decimal_mul", "decimal_div",
        "decimal_neg", "decimal_compare", "decimal_eq",
        "decimal_round", "decimal_abs",
    })

    _JSON_BUILTINS = frozenset({
        "json_parse", "json_stringify",
    })

    _HTML_BUILTINS = frozenset({
        "html_parse", "html_to_string", "html_query", "html_text",
    })

    # Math host-imported builtins (#467).  Only the log/trig ops —
    # pi/e and sign/clamp/float_clamp are inlined as WAT, no
    # host import needed.
    _MATH_BUILTINS = frozenset({
        "log", "log2", "log10",
        "sin", "cos", "tan", "asin", "acos", "atan", "atan2",
    })

    def _scan_io_ops(self, node: ast.Node) -> None:
        """Walk a function body looking for IO, Markdown, and Regex builtins.

        Registers each distinct IO operation name (print, read_line, etc.)
        into ``_io_ops_used`` for per-operation import emission.  Also
        registers Markdown host-import builtins into ``_md_ops_used``
        and regex host-import builtins into ``_regex_ops_used``.

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (recurses into sub-exprs that may contain registrable calls):
        #   QualifiedCall     → registers IO/Http/Inference/Random op
        #                       then recurses into args
        #   FnCall            → registers Markdown/Regex/Map/Set/Decimal/
        #                       Json/Html/Math builtin then recurses args
        #   Block             → recurses into each statement (LetStmt,
        #                       LetDestruct, ExprStmt) + the trailing expr
        #   LetStmt           → recurses into the bound value
        #   LetDestruct       → recurses into the destructured value
        #                       (#1210 round 5 — a destructuring `let` was
        #                       absent from this walk ENTIRELY, so
        #                       `let Tuple<@String, @String> =
        #                       pairs(md_to_html("# hi"))` reached the
        #                       lowering with no import registered)
        #   ExprStmt          → recurses into the statement's expr
        #   ConstructorCall   → recurses into each arg
        #   BinaryExpr        → recurses into left + right
        #   UnaryExpr         → recurses into operand
        #   IfExpr            → recurses into cond + then + else
        #   MatchExpr         → recurses into scrutinee + arm bodies
        #   HandleExpr        → recurses into body
        #   IndexExpr         → recurses into collection + index
        #                       (defensive add #597 — masked today by
        #                       type checker rejecting IO in index
        #                       positions, but plugs the gap if a
        #                       host-imported Int-returning builtin
        #                       lands in the future)
        #   ArrayLit          → recurses into each element (defensive
        #                       add #597 — masked today by the [E602]
        #                       path dropping IO-in-ArrayLit functions)
        #   InterpolatedString → recurses into each Expr part
        #                       (defensive add #597 — same masking as
        #                       ArrayLit)
        #   AnonFn            → recurses into body (defensive add
        #                       #597 — IS the primary defence: pr-
        #                       review of #668 surfaced that
        #                       `_compile_lifted_closure` in
        #                       `vera/codegen/closures.py` does NOT
        #                       call this scanner on lifted bodies,
        #                       so without this branch IO ops
        #                       inside a closure body would silently
        #                       miss their host-import registration)
        #                       AND into the SIGNATURE's refinement
        #                       predicates (#1210 round 7, via
        #                       `_scan_anon_fn_signature`): a refined
        #                       formal / return is guarded in that
        #                       same lifted body
        #   AssertExpr        → recurses into the condition (#1210
        #                       round 2 — pure ≠ host-import-free: an
        #                       `md_*` / `regex_*` builtin, or a
        #                       handler clause reached through one,
        #                       registers its import only here)
        #   AssumeExpr        → recurses into the condition
        #   ForallExpr        → recurses into domain + predicate
        #   ExistsExpr        → recurses into domain + predicate
        #   ModuleCall        → recurses into each arg (#1210 round 5).
        #                       The CALLEE is the imported module's own
        #                       scan to register; the ARGUMENTS are this
        #                       module's expressions and are lowered
        #                       here, so the previous "tracked by that
        #                       module's scan" disposition covered only
        #                       half the node
        #
        # Intentionally ignored (leaves — no sub-exprs to recurse into):
        #   IntLit            → leaf
        #   FloatLit          → leaf
        #   BoolLit           → leaf
        #   StringLit         → leaf
        #   UnitLit           → leaf
        #   SlotRef           → leaf
        #   ResultRef         → leaf
        #   NullaryConstructor → zero-arg, no sub-exprs
        #   OldExpr           → names an EffectRef, not an expression
        #   NewExpr           → names an EffectRef, not an expression
        #
        # Cannot occur:
        #   HoleExpr          → parser placeholder, check-time rejects
        """
        if isinstance(node, ast.QualifiedCall):
            if node.qualifier == "IO":
                self._io_ops_used.add(node.name)
            elif node.qualifier == "Http":
                self._http_ops_used.add(f"http_{node.name}")
            elif node.qualifier == "Inference":
                self._inference_ops_used.add(f"inference_{node.name}")
            elif node.qualifier == "DB":
                self._db_ops_used.add(f"db_{node.name}")  # #229
            elif node.qualifier == "Random":
                # #465 — op names already begin with `random_`
                # (`random_int`/`random_float`/`random_bool`), which
                # both reads naturally at the call site and prevents
                # collision with bare `int`/`float`/`bool` user
                # effect ops.  Track the name directly.
                self._random_ops_used.add(node.name)
            for arg in node.args:
                self._scan_io_ops(arg)
            return
        if isinstance(node, ast.Block):
            for stmt in node.statements:
                # #1210 round 5: `LetDestruct` — a destructuring `let` — was
                # missing here, so its value expression was never walked while
                # codegen lowered it like any other.
                if isinstance(stmt, (ast.LetStmt, ast.LetDestruct)):
                    self._scan_io_ops(stmt.value)
                elif isinstance(stmt, ast.ExprStmt):
                    self._scan_io_ops(stmt.expr)
            self._scan_io_ops(node.expr)
        elif isinstance(node, ast.FnCall):
            # #841: fused-async interception — must agree exactly with
            # the WasmContext translation (shared predicates in
            # vera/wasm/async_fusion.py).  A fused async(Http.get(...))
            # registers the async_http_* import INSTEAD of the sync
            # http_* the QualifiedCall branch would register when the
            # walk reached the inner call; an await that needs the
            # fused-handle runtime check additionally registers
            # async_await (its argument is still scanned normally).
            fused = fused_async_target(node)
            if fused is not None:
                self._async_ops_used.add(fused)
                inner = node.args[0]
                assert isinstance(inner, ast.QualifiedCall)  # noqa: S101
                for arg in inner.args:
                    self._scan_io_ops(arg)
                return
            # NOTE: this pre-scan registration is redundant-but-benign for
            # await — the WasmContext translation's single registration
            # site in calls_markup.py already guarantees the import ⟺
            # check ⟺ host coherence.  It is kept so the two passes call
            # the shared predicate with identical inputs (the module
            # docstring's "both passes MUST agree" invariant) rather
            # than one of them silently drifting.
            if (
                node.name == "await"
                and len(node.args) == 1
                and await_needs_check(
                    node.args[0],
                    self._future_ret_fns,
                    self._future_ret_module_fns,
                    self._type_aliases,
                    self._type_alias_params,
                )
            ):
                self._async_ops_used.add("async_await")
            if node.name in self._MD_BUILTINS:
                self._md_ops_used.add(node.name)
            if node.name in self._REGEX_BUILTINS:
                self._regex_ops_used.add(node.name)
            if node.name in self._MAP_BUILTINS:
                self._map_ops_used.add(node.name)
            if node.name in self._SET_BUILTINS:
                self._set_ops_used.add(node.name)
            if node.name in self._DECIMAL_BUILTINS:
                self._decimal_ops_used.add(node.name)
            if node.name in self._JSON_BUILTINS:
                self._json_ops_used.add(node.name)
            if node.name in self._HTML_BUILTINS:
                self._html_ops_used.add(node.name)
            if node.name in self._MATH_BUILTINS:
                self._math_ops_used.add(node.name)
            for arg in node.args:
                self._scan_io_ops(arg)
        elif isinstance(node, ast.ConstructorCall):
            for arg in node.args:
                self._scan_io_ops(arg)
        elif isinstance(node, ast.BinaryExpr):
            self._scan_io_ops(node.left)
            self._scan_io_ops(node.right)
        elif isinstance(node, ast.UnaryExpr):
            self._scan_io_ops(node.operand)
        elif isinstance(node, ast.IfExpr):
            self._scan_io_ops(node.condition)
            self._scan_io_ops(node.then_branch)
            if node.else_branch:
                self._scan_io_ops(node.else_branch)
        elif isinstance(node, ast.MatchExpr):
            self._scan_io_ops(node.scrutinee)
            for arm in node.arms:
                self._scan_io_ops(arm.body)
        elif isinstance(node, ast.HandleExpr):
            # All four sub-expression positions, matching
            # `_scan_expr_for_handlers` (#1210): a host-imported builtin
            # reached only from a state-init expression, a clause body, or a
            # clause's `with` update would otherwise emit an orphaned
            # `call $vera.<name>` with no import declaration.
            if node.state is not None:
                self._scan_io_ops(node.state.init_expr)
            for clause in node.clauses:
                self._scan_io_ops(clause.body)
                if clause.state_update is not None:
                    self._scan_io_ops(clause.state_update[1])
            self._scan_io_ops(node.body)
        # Defensive sub-expr recursion (#597) — three of the four
        # branches below (IndexExpr, ArrayLit, InterpolatedString)
        # are masked today by type-checker rules and the [E602]
        # codegen-skip path; the AnonFn branch is the PRIMARY
        # defence — the closure compile pipeline does not call
        # this scanner on lifted bodies (verified by pr-review
        # audit on #668), so IO ops inside a closure body would
        # silently miss their host-import registration without
        # this branch.
        elif isinstance(node, ast.IndexExpr):
            self._scan_io_ops(node.collection)
            self._scan_io_ops(node.index)
        elif isinstance(node, ast.ArrayLit):
            for elem in node.elements:
                self._scan_io_ops(elem)
        elif isinstance(node, ast.InterpolatedString):
            for part in node.parts:
                # Parts are str (literal) or Expr (interpolated).
                if not isinstance(part, str):
                    self._scan_io_ops(part)
        elif isinstance(node, ast.AnonFn):
            # Body AND signature (#1210 round 7): a refined formal / return
            # has its predicate lowered as a boundary guard in the lifted
            # body, so an `md_*` / `regex_*` builtin written in one is
            # emitted from here and registered by nobody else.
            self._scan_anon_fn_signature(node, self._scan_io_ops)
            self._scan_io_ops(node.body)
        # #1210 round 2 — symmetrical with `_scan_expr_for_handlers`.  The
        # handler walk now descends these positions, so a handler reached
        # through one is lowered; anything its clause bodies call has to be
        # registered from here or the module references an undeclared import.
        elif isinstance(node, (ast.AssertExpr, ast.AssumeExpr)):
            self._scan_io_ops(node.expr)
        elif isinstance(node, (ast.ForallExpr, ast.ExistsExpr)):
            self._scan_io_ops(node.domain)
            self._scan_io_ops(node.predicate)
        # #1210 round 5 — the CALLEE crosses a module boundary, the ARGUMENTS
        # do not: they are this module's expressions, lowered into this
        # module's body.  Both coverage tables used to dismiss the whole node
        # as the imported module's business.
        elif isinstance(node, ast.ModuleCall):
            for arg in node.args:
                self._scan_io_ops(arg)

    def _scan_body_for_state_handlers(
        self, node: ast.Node, decl: ast.FnDecl | None = None,
    ) -> bool:
        """Walk a function registering every handler's State/Exn family.

        The ENTRY POINT for the handler walk — ``_scan_expr_for_handlers``
        does the recursion, this owns the per-function verdict.

        Covers the body, every contract predicate (``requires`` / ``ensures``
        / ``decreases``) which ``contract_exprs`` enumerates, AND every
        signature refinement predicate which
        ``_signature_refinement_predicates`` enumerates — for this function's
        own signature here, and for every closure signature met on the way
        through the body (``_scan_anon_fn_signature``).  Runtime-checked
        contracts and refinement boundary guards are lowered into the function
        like any other code, so a ``handle[State<Nat>]`` written in a
        ``requires`` predicate (#1210 round 2), in a parameter type's
        ``{ @Int | … }`` refinement (round 5), in a tuple COMPONENT's
        refinement, or in a closure formal's (round 7) emits ``call
        $vera.state_push_Nat`` — the body-only walk registered nothing for it
        and the module failed to compile with ``unknown func``, from a
        check-green, verify-clean program.

        Returns ``False`` when a ``handle[State<T>]`` / ``handle[Exn<E>]``
        reached from *node* names a cell or payload type the backend cannot
        compile, having emitted the same ``E607`` / ``E612`` the
        declared-effect gate emits; the caller drops the function.  Both used
        to be skipped in SILENCE while the lowering emitted ``state_push_…``
        / ``throw $exn_…`` for them regardless.
        """
        self._unregistrable_state_cells: list[tuple[ast.TypeExpr, str]] = []
        self._unregistrable_exn_tags: list[tuple[ast.TypeExpr, str]] = []
        self._scan_expr_for_handlers(node)
        if decl is not None:
            for pred in contract_exprs(decl.contracts):
                self._scan_expr_for_handlers(pred)
            for refined in self._signature_refinement_predicates(decl):
                self._scan_expr_for_handlers(refined)
        fn_name = decl.name if decl is not None else "<unknown>"
        if self._unregistrable_state_cells:
            offender, reason = self._unregistrable_state_cells[0]
            self._warn_unsupported_state_cell(
                offender if getattr(offender, "span", None)
                else (decl or offender),
                fn_name,
                reason,
            )
            return False
        if self._unregistrable_exn_tags:
            offender, reason = self._unregistrable_exn_tags[0]
            self._warn_unsupported_exn_tag(
                offender if getattr(offender, "span", None)
                else (decl or offender),
                fn_name,
                reason,
            )
            return False
        return True

    def _register_scanned_handler(self, node: ast.HandleExpr) -> None:
        """Register the State/Exn family of one ``handle`` expression.

        Shares `_register_state_cell` / `_register_exn_tag` with the
        declared-effect gate, so both registration paths key ONE family
        (#1209) and accept exactly one set of cell types (#1210) — a handler
        declared in a body must not register an import its own lowering never
        calls, nor emit calls to one it never registered.

        The two arms are symmetric on purpose: each records the type it could
        NOT register so the entry point can emit the declared-effect gate's
        own diagnostic and drop the function.  The Exn arm used to discard the
        verdict, so `handle[Exn<Unit>]` in a `pure` function registered no tag
        and still compiled — `unknown tag $exn_Unit` at WAT, where the
        declared-row twin was a clean E612 function drop.
        """
        if not isinstance(node.effect, ast.EffectRef):
            return
        if not node.effect.type_args or len(node.effect.type_args) != 1:
            # Arity is the checker's E337; nothing to register either way.
            return
        type_arg = node.effect.type_args[0]
        if node.effect.name == "State":
            reason = self._register_state_cell(type_arg)
            if reason is not None:
                self._unregistrable_state_cells.append((type_arg, reason))
        elif node.effect.name == "Exn":
            reason = self._register_exn_tag(type_arg)
            if reason is not None:
                self._unregistrable_exn_tags.append((type_arg, reason))

    def _scan_expr_for_handlers(self, node: ast.Node) -> None:
        """Recurse into expressions looking for HandleExpr nodes.

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (recurses into sub-exprs that may contain HandleExpr):
        #   HandleExpr        → registers State<T>/Exn<E> types, then
        #                       recurses into ALL FOUR sub-expression
        #                       positions: the state-init expression, each
        #                       clause body, each clause's `with` update,
        #                       and the handled body.  The walk used to
        #                       descend the body ALONE (#1210), so a family
        #                       reached only from one of the other three was
        #                       never registered while the lowering emitted
        #                       its calls — `unknown func
        #                       $vera.state_push_Nat` at whole-module WAT
        #                       compilation, from a check-green program.
        #   Block             → recurses into each statement (LetStmt,
        #                       LetDestruct, ExprStmt) + the trailing expr
        #   LetStmt           → recurses into the bound value
        #   LetDestruct       → recurses into the destructured value
        #                       (#1210 round 5 — a destructuring `let` was
        #                       absent from this walk ENTIRELY, so
        #                       `let Tuple<@Nat, @Nat> =
        #                       pairn(handle[State<Nat>] … )` emitted
        #                       `state_push_Nat` against no import, and
        #                       an `Exn<Unit>` payload there bypassed the
        #                       round-3 E612 gate outright)
        #   ExprStmt          → recurses into the statement's expr
        #   FnCall            → recurses into each arg
        #   ConstructorCall   → recurses into each arg
        #   BinaryExpr        → recurses into left + right
        #   UnaryExpr         → recurses into operand
        #   IfExpr            → recurses into cond + then + else
        #   MatchExpr         → recurses into scrutinee + arm bodies
        #   QualifiedCall     → recurses into args (defensive add #597)
        #   IndexExpr         → recurses into collection + index
        #                       (defensive add #597)
        #   ArrayLit          → recurses into each element
        #                       (defensive add #597)
        #   InterpolatedString → recurses into each Expr part
        #                       (defensive add #597)
        #   AnonFn            → recurses into body (defensive add #597 —
        #                       IS the primary defence: the closure
        #                       compile pipeline does not run its own
        #                       handler scan on lifted bodies, so
        #                       without this branch HandleExprs inside
        #                       a closure body would silently miss
        #                       their State/Exn host-import
        #                       registration) AND into the SIGNATURE's
        #                       refinement predicates (#1210 round 7,
        #                       via `_scan_anon_fn_signature`): the
        #                       closure path guards a refined formal /
        #                       return in that same lifted body, so
        #                       `fn(@Big -> @Int)` behind an `apply_fn`
        #                       emitted `state_push_Nat` against an
        #                       import nothing declared
        #   AssertExpr        → recurses into the condition (#1210
        #                       round 2 — "pure" is not "handler-free":
        #                       `assert(handle[State<Nat>] … > 0)` is
        #                       check-green and LOWERED, so refusing to
        #                       descend left `state_push_Nat` undeclared)
        #   AssumeExpr        → recurses into the condition (same shape;
        #                       verifier-only today, kept symmetric so
        #                       the two cannot drift)
        #   ForallExpr        → recurses into domain + predicate
        #   ExistsExpr        → recurses into domain + predicate
        #   ModuleCall        → recurses into each arg (#1210 round 5).
        #                       Only the CALLEE is the imported module's
        #                       to register; the ARGUMENTS are this
        #                       module's expressions, lowered here.  The
        #                       old "tracked by that module's own scan"
        #                       disposition was true of the callee and
        #                       false of the args, and
        #                       `vera.math::identn(handle[State<Nat>] … )`
        #                       compiled to `unknown func`
        #
        # Intentionally ignored (leaves — no sub-exprs to walk):
        #   IntLit            → leaf
        #   FloatLit          → leaf
        #   BoolLit           → leaf
        #   StringLit         → leaf
        #   UnitLit           → leaf
        #   SlotRef           → leaf
        #   ResultRef         → leaf
        #   NullaryConstructor → zero-arg, no sub-exprs
        #   OldExpr           → names an EffectRef, not an expression
        #   NewExpr           → names an EffectRef, not an expression
        #
        # Cannot occur:
        #   HoleExpr          → parser placeholder, check-time rejects
        """
        if isinstance(node, ast.HandleExpr):
            self._register_scanned_handler(node)
            if node.state is not None:
                self._scan_expr_for_handlers(node.state.init_expr)
            for clause in node.clauses:
                self._scan_expr_for_handlers(clause.body)
                if clause.state_update is not None:
                    self._scan_expr_for_handlers(clause.state_update[1])
            self._scan_expr_for_handlers(node.body)
            return
        if isinstance(node, ast.Block):
            for stmt in node.statements:
                # #1210 round 5: `LetDestruct` — a destructuring `let` — was
                # missing here, so a handler in its value registered nothing
                # while the lowering emitted the family's calls, AND the
                # round-3 uncompilable-payload gate never saw the handler at
                # all (`handle[Exn<Unit>]` there compiled to `unknown tag`
                # where its `LetStmt` twin is a clean E612 function drop).
                if isinstance(stmt, (ast.LetStmt, ast.LetDestruct)):
                    self._scan_expr_for_handlers(stmt.value)
                elif isinstance(stmt, ast.ExprStmt):
                    self._scan_expr_for_handlers(stmt.expr)
            self._scan_expr_for_handlers(node.expr)
        elif isinstance(node, ast.FnCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.ConstructorCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.BinaryExpr):
            self._scan_expr_for_handlers(node.left)
            self._scan_expr_for_handlers(node.right)
        elif isinstance(node, ast.UnaryExpr):
            self._scan_expr_for_handlers(node.operand)
        elif isinstance(node, ast.IfExpr):
            self._scan_expr_for_handlers(node.condition)
            self._scan_expr_for_handlers(node.then_branch)
            if node.else_branch:
                self._scan_expr_for_handlers(node.else_branch)
        elif isinstance(node, ast.MatchExpr):
            self._scan_expr_for_handlers(node.scrutinee)
            for arm in node.arms:
                self._scan_expr_for_handlers(arm.body)
        # Defensive sub-expr recursion (#597) — symmetrical with
        # `_scan_io_ops`.  The QualifiedCall / IndexExpr / ArrayLit
        # / InterpolatedString branches are masked today by type-
        # checker rules and the [E602] codegen-skip path.  The
        # AnonFn branch is the PRIMARY defence — the closure
        # compile pipeline does not call this scanner on lifted
        # bodies, so HandleExprs inside a closure body would
        # silently miss their State/Exn host-import registration
        # without this branch.
        elif isinstance(node, ast.QualifiedCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.IndexExpr):
            self._scan_expr_for_handlers(node.collection)
            self._scan_expr_for_handlers(node.index)
        elif isinstance(node, ast.ArrayLit):
            for elem in node.elements:
                self._scan_expr_for_handlers(elem)
        elif isinstance(node, ast.InterpolatedString):
            for part in node.parts:
                if not isinstance(part, str):
                    self._scan_expr_for_handlers(part)
        elif isinstance(node, ast.AnonFn):
            # Body AND signature (#1210 round 7) — the closure path emits a
            # boundary guard for every refined formal and for a refined
            # return, and (since #1235) for each refined component of a tuple
            # formal or return, so a `handle[State<Nat>]` in one of those
            # predicates is lowered into the lifted body with nothing else to
            # register it.
            self._scan_anon_fn_signature(node, self._scan_expr_for_handlers)
            self._scan_expr_for_handlers(node.body)
        # #1210 round 2 — the contract-predicate positions.  These are not
        # "cannot occur": a handle expression is an ordinary Bool-valued
        # expression, so it type-checks inside an `assert` condition or a
        # quantifier predicate, and codegen lowers it there.  Refusing to
        # descend registered nothing while the lowering emitted the calls.
        elif isinstance(node, (ast.AssertExpr, ast.AssumeExpr)):
            self._scan_expr_for_handlers(node.expr)
        elif isinstance(node, (ast.ForallExpr, ast.ExistsExpr)):
            self._scan_expr_for_handlers(node.domain)
            self._scan_expr_for_handlers(node.predicate)
        # #1210 round 5 — symmetrical with `_scan_io_ops`: a module call's
        # ARGUMENTS are this module's expressions, however the callee is
        # registered.
        elif isinstance(node, ast.ModuleCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
