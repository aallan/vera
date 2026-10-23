"""Mixin for function compilability checks.

Determines whether a function can be compiled to WASM based on its
effects, parameter types, and return type, and refuses one whose handler
names a `State` cell or an `Exn` payload no lowering exists for.  A cell or
tag is declared by the code that uses it (`_declare_state_cell`,
`_declare_exn_tag`), never by these checks (#1744).
"""

from __future__ import annotations

from collections.abc import Callable

from vera import ast, fold
from vera.lowering import (
    contract_exprs,
    effect_row_entry_refusal,
    exn_payload_lowerable,
    state_cell_lowerable,
)
from vera.narrowing import MEMORY_EFFECTS
from vera.monomorphize import mangle_type_name
from vera.wasm import WasmContext
from vera.wasm.helpers import CellNames

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


class CompilabilityMixin:
    """Methods for checking if functions are compilable to WASM."""

    def _scan_anon_fn_signature(
        self, node: ast.AnonFn, scan: Callable[[ast.Node], None],
    ) -> None:
        """Walk the boundary-guard predicates of a closure's SIGNATURE (#1210
        round 7), for the handler walk.

        The walk descends an `AnonFn`'s BODY because the closure compile
        pipeline runs no walk of its own on lifted bodies.  Its SIGNATURE is
        lowered there too: `closures.py` emits a runtime guard for every
        refined formal and for a refined return, so a handler in the
        predicate of `Big` in `fn(@Big -> @Int)` is lowered in the lifted
        body, and its cell is judged here.  `_signature_refinement_predicates`
        is the ONE derivation of what those guards check; this walks what it
        yields, and the derivation reports E618 once per site.

        Cycle-guarded, because a refinement predicate may contain a closure
        whose own formal is refined by the same alias: `type R = { @Int | …
        fn(@R -> @Int) … }` type-checks, and expanding R's predicate reaches
        that closure, whose signature expands R's predicate again.  The stack
        is popped on the way out, so this suppresses only genuine re-entry —
        a later function meeting the same closure still gets its own verdict,
        its own E607/E612.
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

        Accepts pure functions, the built-in effects, and State<T> and
        Exn<E> where T and E are compilable types.
        """
        effect = decl.effect
        if isinstance(effect, ast.PureEffect):
            pass  # OK
        elif isinstance(effect, ast.EffectSet):
            for eff in effect.effects:
                if isinstance(eff, ast.EffectRef):
                    # The backstop for rule 6 (`vera.lowering`, #1681): the
                    # checker refuses a user-declared effect, State or Exn
                    # without a type argument, and a row variable in this,
                    # the function's own row, where the row names it (E340).
                    # This dropped the function before the rule moved to the
                    # check.  A clone's row variable is no
                    # longer one of its `forall` variables, and is refused as
                    # an effect the roster lacks.  The roster is the one the
                    # verifier reads to decide whether an operation argument
                    # can be guarded at all (#754).
                    refusal = effect_row_entry_refusal(
                        eff.name, len(eff.type_args or ()),
                        row_variable=eff.name in (decl.forall_vars or ()),
                        declaration=True)
                    if refusal is not None:
                        self._error(
                            eff,
                            f"Internal compiler error: the effect row entry "
                            f"'{eff.name}' of '{decl.name}' reached code "
                            f"generation, and "
                            f"vera.lowering.effect_row_entry_refusal refuses "
                            f"it ({refusal}); the checker refuses it at the "
                            f"row (E340).",
                            rationale=(
                                "This is a codegen invariant violation — the "
                                "type checker should have rejected the input "
                                "before it reached this point.  Please file a "
                                "bug report with the offending program."
                            ),
                            error_code="E699",
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
                    error_code="E600",
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
                error_code="E601",
            )
            return False

        return True

    def _check_state_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Refuse a State<T> effect whose cell has no lowering (E607).

        Returns True if compilable, False otherwise.  The row declares
        nothing: the cell is declared by the code that calls it
        (`_declare_state_cell`), so a function code generation drops
        declares none (#1744).
        """
        # One type argument: rule 6 (`effect_row_entry_refusal`) is asked
        # first, in `_is_compilable`.
        assert eff.type_args is not None and len(eff.type_args) == 1  # noqa: S101
        type_arg = eff.type_args[0]
        reason = self._state_cell_refusal(type_arg)
        if reason is not None:
            self._warn_unsupported_state_cell(decl, decl.name, reason)
            return False
        return True

    def _state_cell_refusal(
        self, type_arg: ast.TypeExpr,
    ) -> str | None:
        """Why `State<type_arg>` has no cell code generation can lower, or
        ``None`` when it has one.

        The ONE place a State cell's compilability is decided, shared by the
        declared-effect gate (`_check_state_type`) and the handler walk
        (`_scan_expr_for_handlers`) — the two paths must accept exactly the
        same cell types, or a handler discharging the effect inside a `pure`
        function lowers calls to a cell no gate refused (#1210:
        `handle[State<String>]` was check-green invalid WASM).

        The import FAMILY is the cell the CHECKER typed (#1209), so every
        alias spelling that resolves to it — scalar (#1205), composite,
        parameterised — is ONE family, and the length the symbol cap is held
        to is the mangled family's.
        """
        wt = self._type_expr_to_wasm_type(type_arg)
        if not state_cell_lowerable(
                representable=wt is not None and wt != "unsupported",
                pair=wt == "i32_pair"):
            # THE rule (`vera.lowering.state_cell_lowerable`), read by the
            # checker and the verifier too: a cell's value crosses host
            # imports that carry one word, so a `(ptr, len)` pair has no way
            # through whatever the write guard could bind.  The checker
            # refuses a cell written in the source (E340, #1512); what
            # reaches here is a `State<T>` clone instantiated at such a type
            # (#1679).  Sharing the rule is what stops the obligation stream
            # recording a runtime check for a write inside a function this
            # refusal drops (#1439).
            return UNSUPPORTED_CELL_TYPE
        return _oversized_family_reason(self._family_name_te(type_arg))

    def _declare_state_cell(
        self, family: str, type_arg: ast.TypeExpr,
    ) -> None:
        """Declare the cell *family*, which emitted code calls (#1744).

        Each emitter of a cell's call records the cell on its function's
        context, under the family its calls are named by and the type
        expression it was written at; the record joins the module's here,
        at the per-function and the closure merge, as the host imports'
        does (#735).  The cell's four imports are declared in the order the
        cells are first used, at the width `wt`, derived from the RESOLVED
        type, so every alias spelling of one cell is one declaration
        (#1205), and its representation name `base` beside it (#1218).
        """
        cell = CellNames(family=family, base=self._family_base_te(type_arg))
        wt = self._type_expr_to_wasm_type(type_arg)
        if cell.family and (cell, wt) not in self._state_types:
            self._state_types.append((cell, wt))

    def _warn_unsupported_state_cell(
        self, node: ast.Node, fn_name: str,
        reason: str = UNSUPPORTED_CELL_TYPE,
    ) -> None:
        """The E607 both State-cell paths emit — one wording, one code.

        *reason* selects between the two refusals `_state_cell_refusal`
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
            rationale=(
                "A State<T> cell's value crosses host imports that carry one "
                "word, so a cell whose value is a (ptr, len) pair (String, "
                "Array<T>) or has no representation (Unit, Never) is not "
                "lowered; scalar, compound, data and Map cells are.  The "
                "checker refuses such a cell where it is written (E340); "
                "this one is a State<T> cell instantiated at such a type.  "
                "Wrap the value in a one-constructor data type and "
                "instantiate at that: private data Text { T(String) }."
            ),
            error_code="E607",
        )

    def _check_exn_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Refuse an Exn<E> effect whose payload has no lowering (E612).

        Returns True if compilable, False otherwise.  The row declares
        nothing: the tag is declared by the code that throws or catches it
        (`_declare_exn_tag`), so a function code generation drops declares
        none (#1744).
        """
        # One type argument: rule 6 (`effect_row_entry_refusal`) is asked
        # first, in `_is_compilable`.
        assert eff.type_args is not None and len(eff.type_args) == 1  # noqa: S101
        type_arg = eff.type_args[0]
        reason = self._exn_tag_refusal(type_arg)
        if reason is not None:
            self._warn_unsupported_exn_tag(decl, decl.name, reason)
            return False
        return True

    def _warn_unsupported_exn_tag(
        self, node: ast.Node, fn_name: str,
        reason: str = UNSUPPORTED_CELL_TYPE,
    ) -> None:
        """The E612 both Exn-tag paths emit — one wording, one code.

        The `_warn_unsupported_state_cell` twin.  Both refusing paths (the
        declared-effect gate and the handler walk) must reach the same
        verdict on the same payload type, or a handler discharging `Exn<E>`
        inside a `pure` function lowers `throw $exn_E` / `catch $exn_E` for a
        payload no gate refused — `unknown tag $exn_Unit` at whole-module WAT
        compilation, from a check-green program (#1210).

        *reason* selects between the two refusals exactly as the State twin
        does.  The oversized-family one applies here for symmetry rather
        than for the same hazard: a tag name is a WAT-text identifier that
        the encoder resolves to an index, so it never becomes a name string
        and cannot cross the 100,000-byte cap.  Refusing both keeps ONE
        answer to "is this family emittable?" — the two refusing paths
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
            rationale=(
                "An Exn<E> payload is thrown as a WebAssembly tag's "
                "parameters, so a payload with no representation (Unit, "
                "Never) has nothing to throw.  The checker refuses such a "
                "payload where it is written (E340); this one is an Exn<E> "
                "handler or row instantiated at such a type.  Throw a value: "
                "Exn<Bool>, or a one-constructor data type such as "
                "private data Failure { Failed }."
            ),
            error_code="E612",
        )

    def _exn_tag_refusal(self, type_arg: ast.TypeExpr) -> str | None:
        """Why `Exn<type_arg>` has no tag code generation can lower, or
        ``None`` when it has one.

        The State twin (`_state_cell_refusal`): one rule shared by the
        declared-effect gate and the handler walk, so a payload one of them
        refuses is never lowered by the other's route (#1210).  Unlike a
        State cell, an `i32_pair` payload IS compilable: the tag takes two
        i32 params.
        """
        wt = self._type_expr_to_wasm_type(type_arg)
        if not exn_payload_lowerable(
                representable=wt is not None and wt != "unsupported"):
            # THE rule (`vera.lowering.exn_payload_lowerable`): the checker
            # refuses a payload written in the source (E340); what reaches
            # here is an `Exn<E>` clone instantiated at such a type (#1679).
            return UNSUPPORTED_CELL_TYPE
        return _oversized_family_reason(self._family_name_te(type_arg))

    def _declare_exn_tag(self, family: str, type_arg: ast.TypeExpr) -> None:
        """Declare the tag *family*, which emitted code throws or catches
        (#1744).

        The State twin (`_declare_state_cell`): each `throw`, each handler's
        `catch` and each export's boundary records the tag it names, and the
        record joins the module's at the merges.  The tag FAMILY is the
        payload the checker typed, so `Exn<Code>` with `type Code = Int` and
        `Exn<Payload>` with `type Payload = Option<Int>` are one tag with
        their resolved spelling's (#1209), at the width derived from the
        RESOLVED type.
        """
        wt = self._type_expr_to_wasm_type(type_arg)
        wasm_tag_t = "i32 i32" if wt == "i32_pair" else wt
        if family and (family, wasm_tag_t) not in self._exn_types:
            self._exn_types.append((family, wasm_tag_t))

    def _declare_used(self, ctx: WasmContext) -> None:
        """Declare the cells and tags *ctx*'s emitted code uses, in the
        order it first used them (#1744): the per-function merge and the
        closure merge each call this once, beside the host imports' own
        merge (#735)."""
        for family, type_arg in ctx._cells_used.items():
            self._declare_state_cell(family, type_arg)
        for family, type_arg in ctx._tags_used.items():
            self._declare_exn_tag(family, type_arg)

    def _scan_body_for_state_handlers(
        self, node: ast.Node, decl: ast.FnDecl | None = None,
    ) -> bool:
        """Walk a function judging every handler's State/Exn cell.

        The ENTRY POINT for the handler walk — ``_scan_expr_for_handlers``
        does the recursion, this owns the per-function verdict.  The walk
        declares nothing (#1744): a cell or tag is declared by the code that
        uses it, so a handler in a function code generation drops declares
        none.  What it decides is what nothing emitted can: whether the
        function is refused before any of it is emitted.

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
        $vera.state_push_Nat``, so its cell is judged with the body's.

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

    def _judge_scanned_handler(self, node: ast.HandleExpr) -> None:
        """Judge the State/Exn cell of one ``handle`` expression.

        Shares `_state_cell_refusal` / `_exn_tag_refusal` with the
        declared-effect gate, so both paths accept exactly one set of cell
        types (#1210).  The two arms are symmetric on purpose: each records
        the type it refuses so the entry point can emit the declared-effect
        gate's own diagnostic and drop the function.  The Exn arm used to
        discard the verdict, so `handle[Exn<Unit>]` in a `pure` function
        still compiled — `unknown tag $exn_Unit` at WAT, where the
        declared-row twin was a clean E612 function drop.
        """
        if not isinstance(node.effect, ast.EffectRef):
            return
        if not node.effect.type_args or len(node.effect.type_args) != 1:
            # Arity is the checker's E337; nothing to judge either way.
            return
        type_arg = node.effect.type_args[0]
        if node.effect.name == "State":
            reason = self._state_cell_refusal(type_arg)
            if reason is not None:
                self._unregistrable_state_cells.append((type_arg, reason))
        elif node.effect.name == "Exn":
            reason = self._exn_tag_refusal(type_arg)
            if reason is not None:
                self._unregistrable_exn_tags.append((type_arg, reason))

    def _scan_expr_for_handlers(self, node: ast.Node) -> None:
        """Judge the State/Exn cell of every handler under *node*, and walk
        every closure's signature.

        `vera.fold.walk` reaches every position a handler can be written
        in: a handler's own state, body, clauses and `with` updates, which
        the walk once descended the body of alone, so a cell reached only
        from the other three was never judged while the lowering emitted
        its calls (#1210); a destructuring `let`'s value; a module call's
        arguments, which are this module's expressions however the callee is
        registered; an assertion, an assumption and a quantifier, since a
        handler is an ordinary expression and is lowered there; and a
        closure's body, since the closure compile pipeline runs no walk of
        its own on a lifted body.  A closure's SIGNATURE is lowered in that
        body too (#1210 round 7: its refined formals and return are guarded
        there), so `_scan_anon_fn_signature` walks the predicates
        `_signature_refinement_predicates` derives for it, before its body.

        A handler is judged where the walk meets it, in the fold's order, a
        handler's body before its clauses: of the cells or payloads the
        backend cannot compile, the one E607 or E612 names is the first the
        walk meets, and a closure's E618 is reported where the walk meets
        the closure, the order the lowering reports E617 in.
        """
        for found in fold.walk(node):
            if isinstance(found, ast.HandleExpr):
                self._judge_scanned_handler(found)
            elif isinstance(found, ast.AnonFn):
                self._scan_anon_fn_signature(
                    found, self._scan_expr_for_handlers)
