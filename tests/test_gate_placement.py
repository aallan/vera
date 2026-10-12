"""Every gate the local hook runs also runs in CI.

The local pre-commit hook runs the fast gates — lint, types, the doc and
consistency gates, and the test files a commit stages — and CI runs every
one of them again, so a commit that reaches CI without the hook (a
``git rebase --continue``, which runs no hooks, or a contributor who never
installed them) is still gated.  Both halves are read from the
configuration files themselves:

- ``.pre-commit-config.yaml``: no hook runs the whole suite, one of the slow
  sweeps or a count check, and the doc-example hook fires on exactly the
  documents its gate reads.
- ``.github/workflows/ci.yml``: on each event CI runs on (a pull request, a
  pull request that raises ``[project].version``, the push event a merge
  produces on ``main``, a release merge's, and the nightly run), every
  hook's command is a step that runs and can fail the run.  A hook that
  runs pytest over the staged files or the collection is matched by a run
  of the whole suite: one pytest step that nothing narrows, or the cells of
  one sharded job running every shard of one count between them
  (tests/shard.py).  Which job runs a gate, and on which events it runs
  anything else, is the workflow's to say.

Conditions in the workflow (``if:`` keys and ``${{ }}`` expressions) are
evaluated, not string-matched, by the small evaluator below: a condition
that stops matching a cell or an event is a behaviour change, however it is
spelled.  The CI half fails closed.  A step counts as a gate only where it
runs and can fail the run: a condition the evaluator cannot read is an error
unless ``UNREADABLE_CONDITIONS`` names the step with its reason (a condition
on a context name the modelled events do not define is unreadable, not
null), and ``continue-on-error``, a shell other than the default ``bash -e``,
or a run command that swallows its own failure (``|| true``, ``set +e``) is
an error outright.  A gate is a command the step invokes on a line with no
shell control operator, not text it mentions.
"""

from __future__ import annotations

import importlib.util
import itertools
import re
import shlex
from pathlib import Path
from typing import Any

import pytest

# PyYAML arrives with pre-commit, a `[dev]` dependency that reads its own
# configuration with it, so the files are read here the way pre-commit and
# Actions read them rather than by pattern.
import yaml

from tests import shard

ROOT = Path(__file__).resolve().parent.parent
PRECOMMIT = ROOT / ".pre-commit-config.yaml"
CI = ROOT / ".github" / "workflows" / "ci.yml"

# The sweeps too slow for a commit.  CI runs the last three in `lint`; the
# first is a local tool whose work CI does through the suite
# (tests/test_conformance.py), so a hook runs none of them.
SLOW_SWEEPS = (
    "scripts/check_conformance.py",
    "scripts/check_examples.py",
    "scripts/check_examples_run.py",
    "scripts/check_e602_clean.py",
)

# The pre-commit-hooks hooks that CI cannot run as the commit does, and why.
COMMIT_TIME_ONLY = {
    "check-added-large-files": (
        "inspects the files a commit ADDS, which only the commit's own index"
        " records; run over a checkout it has nothing to inspect"
    ),
}

# A local hook's script whose CI counterpart is a different script: the
# generator runs locally, and CI verifies its output is current.
CI_COUNTERPART = {"scripts/build_site.py": "scripts/check_site_assets.py"}


def _hooks() -> list[dict[str, Any]]:
    config = yaml.safe_load(PRECOMMIT.read_text(encoding="utf-8"))
    return [
        {**hook, "repo": repo["repo"]}
        for repo in config["repos"]
        for hook in repo["hooks"]
    ]


def _workflow() -> dict[Any, Any]:
    return dict(yaml.safe_load(CI.read_text(encoding="utf-8")))


def _doc_example_gate() -> Any:
    """scripts/check_doc_examples.py, whose document list the doc-example
    hook's trigger has to follow."""
    path = ROOT / "scripts" / "check_doc_examples.py"
    spec = importlib.util.spec_from_file_location("gate_placement_doc_examples", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module



def _command(line: str) -> list[str]:
    """A shell line's command word and arguments, past any leading `env` and
    `NAME=value` assignments; `[]` for a line that is not a simple command."""
    try:
        tokens = shlex.split(line)
    except ValueError:
        return []
    while tokens and (tokens[0] == "env" or re.fullmatch(r"[A-Za-z_]\w*=\S*", tokens[0])):
        tokens = tokens[1:]
    return tokens


def _runs_pytest(entry: str) -> list[str] | None:
    """The arguments of a command that runs pytest, or None.

    Pytest as the command word (`pytest`, `.venv/bin/pytest`) or as the
    module a Python runs (`python -m pytest`, `.venv/bin/python3 -X dev -m
    pytest`).  The command word, not any token: `echo pytest` runs no
    tests."""
    tokens = _command(entry)
    if not tokens:
        return None
    word = tokens[0].rsplit("/", 1)[-1]
    if word in ("pytest", "py.test"):
        return tokens[1:]
    if re.fullmatch(r"python[\d.]*", word):
        for index in range(1, len(tokens) - 1):
            if tokens[index] == "-m":
                return tokens[index + 2:] if tokens[index + 1] == "pytest" else None
    return None


# ---------------------------------------------------------------------------
# A small evaluator for GitHub Actions expressions: string literals, context
# names, `==` / `!=` (case-insensitive on strings, as Actions compares them),
# `!`, `&&`, `||`, parentheses, and the four status functions — what ci.yml's
# conditions use.  The status functions answer for a run whose earlier steps
# passed, which is the run a gate has to hold in: `always()` and `success()`
# are true, `failure()` and `cancelled()` false.  Anything else is a
# SyntaxError, so a condition this cannot read fails the test that needed it
# rather than being skipped.
# ---------------------------------------------------------------------------

_STATUS_FUNCTIONS = {
    "always": True, "success": True, "failure": False, "cancelled": False,
}

_TOKEN = re.compile(
    r"\s*(?:(?P<op>==|!=|&&|\|\||!|\(|\))|'(?P<str>(?:[^']|'')*)'"
    r"|(?P<name>[A-Za-z_][\w.\-]*))"
)


def _tokens(expr: str) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    pos = 0
    expr = expr.rstrip()
    while pos < len(expr):
        m = _TOKEN.match(expr, pos)
        if m is None or m.end() == pos:
            raise SyntaxError(f"cannot read {expr[pos:]!r} in {expr!r}")
        kind = m.lastgroup
        assert kind is not None
        value = m.group(kind)
        if kind == "str":
            value = value.replace("''", "'")
        out.append((kind, value))
        pos = m.end()
    return out


def evaluate(
    expr: str, context: dict[str, object], strict: bool = True
) -> object:
    """Evaluate one expression, with or without its `${{ }}` wrapper.

    Strict by default: a context name the event (or matrix cell) does not
    define is unreadable, not null, since a condition on `github.actor` or
    `github.head_ref` would otherwise read as `!=` anything and count a step
    the modelled events cannot say runs.  Rendering a `run:` command is
    lenient (`strict=False`): there an unmodelled name only fills in text."""
    body = expr.strip()
    if body.startswith("${{") and body.endswith("}}"):
        body = body[3:-2]
    tokens = _tokens(body)
    pos = 0

    def peek() -> tuple[str, str] | None:
        return tokens[pos] if pos < len(tokens) else None

    def take(value: str) -> None:
        nonlocal pos
        if peek() != ("op", value):
            raise SyntaxError(f"expected {value!r} at {tokens[pos:]!r} in {expr!r}")
        pos += 1

    def truthy(value: object) -> bool:
        return value not in (None, False, "", 0)

    def equal(a: object, b: object) -> bool:
        if isinstance(a, str) and isinstance(b, str):
            return a.lower() == b.lower()
        return a == b

    def atom() -> object:
        nonlocal pos
        token = peek()
        if token is None:
            raise SyntaxError(f"unexpected end of {expr!r}")
        if token == ("op", "("):
            pos += 1
            value = disjunction()
            take(")")
            return value
        kind, text = token
        pos += 1
        if kind == "str":
            return text
        if kind == "name":
            if peek() == ("op", "("):
                if text in _STATUS_FUNCTIONS and tokens[pos + 1: pos + 2] == [("op", ")")]:
                    pos += 2
                    return _STATUS_FUNCTIONS[text]
                raise SyntaxError(f"function call {text}() in {expr!r}")
            if text in ("true", "false"):
                return text == "true"
            if strict and text not in context:
                raise SyntaxError(f"{text} is not defined for this event in {expr!r}")
            return context.get(text)
        raise SyntaxError(f"unexpected {text!r} in {expr!r}")

    # Precedence as Actions defines it: `!` binds tighter than `==` and
    # `!=`, which bind tighter than `&&`, then `||`.  So `!a != 'y'` is
    # `(!a) != 'y'`.
    def negation() -> object:
        nonlocal pos
        if peek() == ("op", "!"):
            pos += 1
            return not truthy(negation())
        return atom()

    def comparison() -> object:
        nonlocal pos
        left = negation()
        token = peek()
        if token in (("op", "=="), ("op", "!=")):
            pos += 1
            right = negation()
            same = equal(left, right)
            return same if token == ("op", "==") else not same
        return left

    def conjunction() -> object:
        nonlocal pos
        value = comparison()
        while peek() == ("op", "&&"):
            pos += 1
            right = comparison()
            value = right if truthy(value) else value
        return value

    def disjunction() -> object:
        nonlocal pos
        value = conjunction()
        while peek() == ("op", "||"):
            pos += 1
            right = conjunction()
            value = value if truthy(value) else right
        return value

    result = disjunction()
    if pos != len(tokens):
        raise SyntaxError(f"trailing {tokens[pos:]!r} in {expr!r}")
    return result


def render(command: str, context: dict[str, object]) -> str:
    """A `run:` command with each `${{ }}` replaced by its value."""

    def value(m: re.Match[str]) -> str:
        result = evaluate(m.group(0), context, strict=False)
        if result is None:
            return ""
        if isinstance(result, bool):
            return "true" if result else "false"
        return str(result)

    return re.sub(r"\$\{\{.*?\}\}", value, command)


def _truthy(value: object) -> bool:
    return value not in (None, False, "", 0)


# Conditions the evaluator cannot read, each allowed with the reason the step
# still gates.  Any other condition it cannot read fails the test that met it:
# a gate's condition is evaluated or justified, never guessed.
UNREADABLE_CONDITIONS = {
    "Check CHANGELOG updated for substantive changes": (
        "skips only a pull request labelled `skip-changelog`, the documented"
        " escape hatch (CONTRIBUTING.md); every other pull request and every"
        " push runs it"
    ),
}

# Matrix cells allowed to fail without failing the run, each with the reason,
# keyed by job and the cell's `matrix.os`.  Such a cell gates nothing; a
# `continue-on-error` that can be true anywhere else is an error.
ADVISORY_CELLS = {
    ("test", "ubuntu-24.04-arm"): (
        "the Linux aarch64 cell is advisory (README § Supported platforms):"
        " the job's `continue-on-error` is its `advisory` matrix value, so a"
        " failure there fails neither the run nor matrix-gate"
    ),
}


def _advisory(job_name: str, job: dict[str, Any], context: dict[str, object]) -> bool:
    """Whether `context` is a cell `ADVISORY_CELLS` names, whose job's
    `continue-on-error` is true there."""
    if (job_name, context.get("matrix.os")) not in ADVISORY_CELLS:
        return False
    value = job.get("continue-on-error")
    try:
        return value is True or (isinstance(value, str) and _truthy(evaluate(value, context)))
    except SyntaxError:
        return False


def _runs(item: dict[str, Any], context: dict[str, object], where: str) -> bool:
    """Whether a job or step runs in `context`, failing closed.

    No `if` runs.  A condition the evaluator reads runs when it is true.  One
    it cannot read runs only if `UNREADABLE_CONDITIONS` names the step, and
    otherwise fails the test that asked rather than counting either way."""
    condition = item.get("if")
    if condition is None:
        return True
    try:
        return _truthy(evaluate(str(condition), context))
    except SyntaxError:
        if item.get("name") in UNREADABLE_CONDITIONS:
            return True
        pytest.fail(
            f"{where}: cannot evaluate `if: {condition}` — teach the evaluator"
            " its form, or name the step in UNREADABLE_CONDITIONS with the"
            " reason it still gates"
        )


def _can_fail(item: dict[str, Any], context: dict[str, object], where: str) -> None:
    """A gate that cannot fail the run is no gate: `continue-on-error` must be
    absent or provably false in `context`, and no shell may be substituted
    for the default `bash -e`, which stops a multi-line step at its first
    failing command."""
    value = item.get("continue-on-error")
    if value not in (None, False):
        try:
            allowed = isinstance(value, str) and not _truthy(evaluate(value, context))
        except SyntaxError:
            allowed = False
        if not allowed:
            pytest.fail(
                f"{where} carries `continue-on-error: {value}`, so it can fail"
                " without failing the run"
            )
    shell = item.get("shell") or (item.get("defaults") or {}).get("run", {}).get("shell")
    if shell is not None:
        pytest.fail(f"{where} runs its steps under `{shell}` instead of the default `bash -e`")


def _gating_steps(
    workflow: dict[Any, Any], job_name: str, context: dict[str, object]
) -> list[dict[str, Any]]:
    """The steps of one job that run in `context` and can fail the run.

    The job's own `if` and `continue-on-error` count, and so do the
    workflow's `defaults`; a job that does not run gates nothing, and
    neither does a cell `ADVISORY_CELLS` names.  A run
    command that swallows its own failure (`|| true`, `set +e`, …) fails the
    test outright: its step is not a gate however the job is configured."""
    _can_fail(workflow, context, "the workflow")
    job = workflow["jobs"][job_name]
    if not _runs(job, context, f"job {job_name}"):
        return []
    if _advisory(job_name, job, context):
        return []
    _can_fail(job, context, f"job {job_name}")
    steps: list[dict[str, Any]] = []
    for step in job.get("steps", []):
        where = f"job {job_name}, step {step.get('name') or step.get('uses')!r}"
        if not _runs(step, context, where):
            continue
        _can_fail(step, context, where)
        command = render(str(step.get("run", "")), context)
        if re.search(r"\|\||\bset\s+\+e\b", command):
            pytest.fail(f"{where}: `{command.strip()}` can swallow its own failure")
        steps.append({**step, "run": command})
    return steps


_CONTROL_OPERATORS = ("|", "|&", "&", "&&", "||", ";")


def _no_control_operator(line: str, what: str) -> None:
    """A line that invokes a gate carries no shell control operator.

    CI's default shell is `bash -e` without `pipefail`, so after `| tee`, a
    trailing `&`, an `&& echo ok` or a `; echo done` the line exits 0 when
    the gate fails."""
    lexer = shlex.shlex(line, posix=True, punctuation_chars=True)
    operators = [token for token in lexer if token in _CONTROL_OPERATORS]
    if operators:
        pytest.fail(f"`{line.strip()}` can exit 0 when {what} fails ({operators})")


def _invokes(steps: list[dict[str, Any]], *command: str) -> list[dict[str, Any]]:
    """The steps with a line whose command word and first arguments are
    `command` — invoked, not merely mentioned (`echo scripts/x.py` is not),
    and invoked so that its failure fails the line."""
    want = list(command)
    found: list[dict[str, Any]] = []
    for step in steps:
        for line in step["run"].splitlines():
            if _command(line)[: len(want)] == want:
                _no_control_operator(line, " ".join(want))
                found.append(step)
                break
    return found


# The events every gate has to hold on: a pull request into main, one that
# raises `[project].version`, the push event a merged pull request produces
# on main (whether or not the merge raised the version), and the nightly
# schedule.  `needs.plan.outputs.release` is the plan job's answer to "does
# this change raise the version?", `true` or `false` on a pull request and a
# push and empty on the nightly run, where its step does not run.
# `needs.plan.outputs.changed` is the files a pull request changes that a
# class-instrument matrix can be decided by, and empty on every other event.
# `needs.test.result` is the full matrix's result as a run in which every
# gate holds sees it: `success` where the matrix runs, `skipped` where it
# stands down.  `needs.matrix-gate.outputs.failed` is the cells matrix-gate
# read as failed from the run's job listing, and in such a run there are
# none.
_WORKFLOW = {"github.workflow": "CI", "needs.matrix-gate.outputs.failed": ""}
_PULL_REQUEST = {
    **_WORKFLOW,
    "github.event_name": "pull_request",
    "github.base_ref": "main",
    "github.ref": "refs/pull/1/merge",
    "needs.plan.outputs.changed": "vera/narrowing.py\ntests/test_one_classifier_1503.py",
}
EVENTS = {
    "pull request into main": {
        **_PULL_REQUEST,
        "needs.plan.outputs.release": "false",
        "needs.test.result": "skipped",
    },
    "pull request that raises the version": {
        **_PULL_REQUEST,
        "needs.plan.outputs.release": "true",
        "needs.test.result": "success",
    },
    "push of a merge into main": {
        **_WORKFLOW,
        "github.event_name": "push",
        "github.base_ref": "",
        "github.ref": "refs/heads/main",
        "github.event.before": "1" * 40,
        "needs.plan.outputs.release": "false",
        "needs.plan.outputs.changed": "",
        "needs.test.result": "skipped",
    },
    "push of a release merge into main": {
        **_WORKFLOW,
        "github.event_name": "push",
        "github.base_ref": "",
        "github.ref": "refs/heads/main",
        "github.event.before": "2" * 40,
        "needs.plan.outputs.release": "true",
        "needs.plan.outputs.changed": "",
        "needs.test.result": "success",
    },
    "nightly schedule": {
        **_WORKFLOW,
        "github.event_name": "schedule",
        "github.base_ref": "",
        "github.ref": "refs/heads/main",
        "github.sha": "3" * 40,
        "needs.plan.outputs.release": "",
        "needs.plan.outputs.changed": "",
        "needs.test.result": "success",
    },
}


class TestTheEvaluator:
    """The evaluator is what the CI tests stand on, so it is tested first."""

    @pytest.mark.parametrize(
        ("expr", "context", "want"),
        [
            ("a == 'x'", {"a": "x"}, True),
            ("a == 'X'", {"a": "x"}, True),
            ("a != 'x'", {"a": "x"}, False),
            ("!(a == 'x')", {"a": "x"}, False),
            ("${{ !(a == 'x' && b == 'y') }}", {"a": "x", "b": "z"}, True),
            ("a == 'x' && '--release' || ''", {"a": "x"}, "--release"),
            ("a == 'x' && '--release' || ''", {"a": "q"}, ""),
            ("(a == 'x' || b == 'y') && 'on' || 'off'", {"a": "q", "b": "y"}, "on"),
            ("always()", {}, True),
            ("success() && a == 'x'", {"a": "x"}, True),
            ("failure() || cancelled()", {}, False),
            ("!a != 'y'", {"a": "x"}, True),
            ("!(a != 'y')", {"a": "x"}, False),
            ("!a == false", {"a": "x"}, True),
        ],
    )
    def test_it_evaluates(
        self, expr: str, context: dict[str, object], want: object
    ) -> None:
        assert evaluate(expr, context) == want

    @pytest.mark.parametrize(
        "expr",
        ["contains(a, 'x')", "always(a)", "a ==", "a b", "a > 'x'", "missing"],
    )
    def test_what_it_cannot_read_is_an_error(self, expr: str) -> None:
        with pytest.raises(SyntaxError):
            evaluate(expr, {"a": "x"})


# ---------------------------------------------------------------------------
# The local hook: fast gates only
# ---------------------------------------------------------------------------


class TestThePreCommitHookIsFast:
    @pytest.mark.parametrize(
        ("entry", "args"),
        [
            ("pytest -q", ["-q"]),
            (".venv/bin/pytest tests/ -q", ["tests/", "-q"]),
            ("python -m pytest tests/", ["tests/"]),
            (".venv/bin/python3.12 -m pytest -q", ["-q"]),
            ("python -X dev -m pytest .", ["."]),
            ("env VERA_EAGER_GC=1 .venv/bin/python -m pytest", []),
            ("echo pytest", None),
            ("python scripts/check_conformance.py", None),
            ("python -m mypy vera/", None),
        ],
    )
    def test_every_spelling_of_pytest_is_recognised(
        self, entry: str, args: list[str] | None
    ) -> None:
        """A pytest invocation the reader missed would be skipped by the
        whole-suite check below, so each spelling is pinned."""
        assert _runs_pytest(entry) == args

    def test_no_hook_runs_the_whole_suite(self) -> None:
        """A hook may run pytest only over the files it is handed, a named
        test file, or collection alone."""
        for hook in _hooks():
            args = _runs_pytest(hook.get("entry", ""))
            if args is None:
                continue
            if "--collect-only" in args or "--co" in args:
                continue
            # Paths, not option values: `-n 4` or `-m "not stress"` names no
            # file.  A node id narrows as its file does.
            paths = [
                a.split("::")[0] for a in args
                if not a.startswith("-") and ("/" in a or a in ("tests", "."))
            ]
            named = [p for p in paths if p.endswith(".py")]
            directories = [p for p in paths if not p.endswith(".py")]
            assert not directories, (
                f"{hook['id']} hands pytest {directories}: a directory is the"
                " whole suite, which runs in CI"
            )
            if named:
                continue
            files = hook.get("files")
            assert hook.get("pass_filenames", True) and files, (
                f"{hook['id']} runs pytest with nothing to narrow it — the"
                " whole suite, which runs in CI"
            )
            # The staged file names are the only narrowing, and `always_run`
            # runs the hook when none match, with no names at all.
            assert not hook.get("always_run"), (
                f"{hook['id']} sets `always_run`, so a commit that stages no"
                " test file runs pytest over the whole suite"
            )
            for path in ("vera/cli.py", "tests/conftest.py", "tests/checker_helpers.py", "scripts/build_site.py"):
                assert not re.search(files, path), (
                    f"{hook['id']} would hand pytest {path}"
                )

    def test_the_staged_test_hook_takes_only_test_files(self) -> None:
        hook = next(h for h in _hooks() if h["id"] == "pytest-staged")
        assert hook.get("pass_filenames", True) is True
        assert hook.get("require_serial") is True
        # A commit that touches a class-instrument matrix runs all of it, not
        # the pull-request gate's sample (tests/matrix_sample.py).
        assert _runs_pytest(hook["entry"]) is not None
        assert "--matrix=full" in (_runs_pytest(hook["entry"]) or []), hook["entry"]
        for path in ("tests/test_parser.py", "tests/test_gate_placement.py"):
            assert re.search(hook["files"], path), path
        for path in (
            "tests/conftest.py",
            "tests/conformance/manifest.json",
            "tests/probes/test_x.py",
            "vera/test_like.py",
        ):
            assert not re.search(hook["files"], path), path

    def test_no_hook_runs_a_slow_sweep(self) -> None:
        for hook in _hooks():
            entry = hook.get("entry", "")
            for script in SLOW_SWEEPS:
                assert script not in entry, (
                    f"{hook['id']} runs {script}, which is too slow for a"
                    " commit"
                )

    def test_no_hook_checks_a_count(self) -> None:
        """A commit never pays for a count.  TESTING.md's generated status
        is written by scripts/render_status.py and checked by
        check_doc_counts.py, and both belong to the release PR, so no hook
        runs either: a fix PR has no count to bring up to date."""
        for hook in _hooks():
            entry = hook.get("entry", "")
            for script in ("scripts/check_doc_counts.py", "scripts/render_status.py"):
                assert script not in entry, f"{hook['id']} runs {script}"

    def test_the_doc_example_hook_fires_on_the_gated_documents_only(self) -> None:
        """The doc-example gate re-verifies every gated block with Z3, so
        its hook fires on the documents the gate reads (`DOC_GATES`) and on
        no other tracked document: a gated document it missed would reach
        CI unchecked, and one outside the list (CHANGELOG.md, TESTING.md)
        re-verified every SKILL and spec block for nothing.  The compiler,
        the examples the blocks import and run, and the gate's own modules
        fire it too.  A document added later with Vera blocks is classified
        by the gate's run over every document, which CI makes."""
        gate = _doc_example_gate()
        files = next(h for h in _hooks() if h["id"] == "doc-examples")["files"]
        gated, errors = gate.expand_gates(ROOT)
        assert errors == []
        documents = gate.tracked_documents(ROOT)
        assert set(gated) <= set(documents)
        wrong = [
            doc for doc in documents
            if (re.search(files, doc) is not None) != (doc in gated)
        ]
        assert wrong == [], (
            f"the hook fires on these exactly when the gate does not read them: {wrong}"
        )
        for path in (
            "vera/checker/core.py",
            "vera/grammar.lark",
            "examples/hello_world.vera",
            "examples/vera/math.vera",
            "scripts/check_doc_examples.py",
            "scripts/check_examples_run.py",
            "scripts/doc_annotations.py",
        ):
            assert re.search(files, path), path


# ---------------------------------------------------------------------------
# CI: every gate the hook runs, on every event
# ---------------------------------------------------------------------------


def _matrix_cells(job: dict[str, Any]) -> list[dict[str, object]]:
    """The cells a job's `strategy.matrix` runs, by GitHub's rules: the
    product of the axes, with each `include` entry added to every cell whose
    axis values it matches, or run as a cell of its own when it matches
    none (an `include`-only matrix is its entries)."""
    matrix = job["strategy"]["matrix"]
    assert "exclude" not in matrix, "the cell arithmetic here ignores exclude"
    axes = {k: v for k, v in matrix.items() if k not in ("include", "exclude")}
    base = [
        dict(zip(axes, values, strict=True))
        for values in itertools.product(*axes.values())
    ] if axes else []
    cells = [dict(cell) for cell in base]
    for extra in matrix.get("include", []):
        fits = [
            index for index, cell in enumerate(base)
            if all(cell[k] == v for k, v in extra.items() if k in axes)
        ]
        for index in fits:
            cells[index].update(extra)
        if not fits:
            cells.append(dict(extra))
    return [{f"matrix.{k}": v for k, v in cell.items()} for cell in cells]


# The arguments that do not narrow what the suite runs: output, workers and
# their scheduling, coverage, and the class-instrument matrices' mode, whose
# sample a pull request runs by design (tests/matrix_sample.py).  `--shard`
# narrows a run to one part, which `_runs_the_whole_suite` reassembles.
# Anything else on a pytest command narrows it.
def _narrowing(args: list[str]) -> list[str]:
    out: list[str] = []
    skip_value = False
    for arg in args:
        if skip_value:
            skip_value = False
            continue
        if arg in ("-v", "-vv", "-q"):
            continue
        if arg in ("-n", "--dist", "--shard"):
            skip_value = True
            continue
        if re.fullmatch(r"--(cov(-report|-fail-under)?|matrix|dist|shard)=\S+", arg):
            continue
        out.append(arg)
    return out


def _shard_of_run(args: list[str]) -> tuple[int, int] | None:
    """The `K/N` a pytest command's `--shard` names, or None for a run of the
    whole collection."""
    for index, arg in enumerate(args):
        if arg.startswith("--shard="):
            return shard.parse_shard(arg.split("=", 1)[1])
        if arg == "--shard" and index + 1 < len(args):
            return shard.parse_shard(args[index + 1])
    return None


def _runs_the_whole_suite(workflow: dict[Any, Any], context: dict[str, object]) -> bool:
    """Whether CI runs the whole suite in `context`: a gating pytest step
    with nothing narrowing it, or the cells of one job whose gating pytest
    steps run every shard `1/N` to `N/N` of one count `N` between them."""
    for name, job in workflow["jobs"].items():
        cells = _matrix_cells(job) if "strategy" in job else [{}]
        shards: dict[int, set[int]] = {}
        for cell in cells:
            for step in _gating_steps(workflow, name, {**context, **cell}):
                for line in step["run"].splitlines():
                    args = _runs_pytest(line)
                    if args is None or _narrowing(args):
                        continue
                    _no_control_operator(line, "pytest")
                    part = _shard_of_run(args)
                    if part is None:
                        return True
                    shards.setdefault(part[1], set()).add(part[0])
        if any(found == set(range(1, count + 1)) for count, found in shards.items()):
            return True
    return False


class TestCiRunsEveryGate:
    """Each gate the hook runs runs in CI on each of the modelled events,
    and can fail the run.

    A step counts only where `_gating_steps` says it runs and can fail: its
    job's and its own conditions evaluated for the event (and matrix cell),
    no `continue-on-error`, no shell substituted for `bash -e`, and no run
    command that swallows its own failure."""

    @pytest.mark.parametrize(
        ("args", "narrows"),
        [
            (["-v", "-n", "auto"], []),
            (["-v", "-n", "4", "--dist", "worksteal", "--shard=2/3"], []),
            (["-n", "auto", "--cov=vera", "--cov-fail-under=80", "--matrix=full"], []),
            (["--dist=worksteal", "--shard", "1/2", "--matrix=sample"], []),
            (["tests/test_browser.py", "-v"], ["tests/test_browser.py"]),
            (["-k", "run"], ["-k", "run"]),
            (["-x", "-q"], ["-x"]),
        ],
    )
    def test_what_narrows_a_run(self, args: list[str], narrows: list[str]) -> None:
        assert _narrowing(args) == narrows

    def test_a_shard_set_is_the_whole_suite_only_when_complete(self) -> None:
        """Three shards of three run the suite; two of them, or shards of
        two different counts, do not."""
        def job(cells: list[dict[str, object]]) -> dict[Any, Any]:
            return {"jobs": {"shard": {
                "strategy": {"matrix": {"include": cells}},
                "steps": [{"run": "pytest -n 4 --shard=${{ matrix.shard }}/${{ matrix.shards }}"}],
            }}}

        context = EVENTS["pull request into main"]
        whole = [{"shard": k, "shards": 3} for k in (1, 2, 3)]
        assert _runs_the_whole_suite(job(whole), context)
        assert not _runs_the_whole_suite(job(whole[:2]), context)
        assert not _runs_the_whole_suite(job([*whole[:2], {"shard": 3, "shards": 4}]), context)
        assert not _runs_the_whole_suite(job([{"shard": 1, "shards": 3}] * 3), context)

    @pytest.mark.parametrize("event", sorted(EVENTS))
    def test_every_gate_the_hook_runs_also_runs_in_ci(self, event: str) -> None:
        workflow = _workflow()
        context = EVENTS[event]
        # A matrix job's step gates when it gates on every cell.
        steps: list[dict[str, Any]] = []
        for name, job in workflow["jobs"].items():
            cells = _matrix_cells(job) if "strategy" in job else [{}]
            per_cell = [
                {step.get("name") or step.get("uses"): step
                 for step in _gating_steps(workflow, name, {**context, **cell})}
                for cell in cells
            ]
            everywhere = set.intersection(*(set(found) for found in per_cell))
            steps += [per_cell[0][key] for key in everywhere]
        # The pre-commit-hooks hooks run in CI through pre-commit itself.
        hygiene = "\n".join(
            step["run"] for step in _invokes(steps, "pre-commit", "run", "--all-files")
        )
        missing: list[str] = []
        for hook in _hooks():
            if hook["repo"] != "local":
                named = re.search(
                    rf"(?<![\w-]){re.escape(hook['id'])}(?![\w-])", hygiene
                )
                if hook["id"] not in COMMIT_TIME_ONLY and named is None:
                    missing.append(f"{hook['id']} (pre-commit run --all-files)")
                continue
            entry = hook["entry"]
            args = _runs_pytest(entry)
            if args is not None:
                # A named test file must be run by name; the staged files and
                # the collection, by a run of the whole suite.
                files = [arg for arg in args if arg.startswith("tests/")]
                for arg in files:
                    if not any(arg in (_runs_pytest(step["run"]) or []) for step in steps):
                        missing.append(f"{hook['id']} ({arg})")
                if not files and not _runs_the_whole_suite(workflow, context):
                    missing.append(f"{hook['id']} (the whole suite)")
                continue
            script = re.search(r"scripts/\w+\.py", entry)
            if script is not None:
                wanted = ["python", CI_COUNTERPART.get(script.group(0), script.group(0))]
            else:
                wanted = _command(entry)
                wanted[0] = wanted[0].removeprefix(".venv/bin/")
            if not _invokes(steps, *wanted):
                missing.append(f"{hook['id']} ({' '.join(wanted)})")
        assert missing == [], f"{event}: local gates CI does not run: {missing}"

    def test_the_commit_time_only_exception_is_real(self) -> None:
        """Every exemption names a hook that exists and that CI does not
        run, so the table cannot outlive its reason."""
        ids = {hook["id"] for hook in _hooks()}
        runs = "\n".join(
            str(step.get("run", ""))
            for job in _workflow()["jobs"].values()
            for step in job.get("steps", [])
        )
        for hook_id in COMMIT_TIME_ONLY:
            assert hook_id in ids
            assert hook_id not in runs

    def test_the_advisory_cells_are_real(self) -> None:
        """Every advisory cell is a cell of its job's matrix where the job's
        `continue-on-error` is true, so the table cannot outlive its reason."""
        workflow = _workflow()
        for job_name, os_name in ADVISORY_CELLS:
            job = workflow["jobs"][job_name]
            cells = [cell for cell in _matrix_cells(job) if cell.get("matrix.os") == os_name]
            assert cells, (job_name, os_name)
            for cell in cells:
                for event, context in EVENTS.items():
                    assert _advisory(job_name, job, {**context, **cell}), (job_name, os_name, event)

    def test_the_unreadable_conditions_are_real(self) -> None:
        """Every allowlisted condition names a step that exists and whose
        condition the evaluator really cannot read, so the table cannot
        outlive its reason either."""
        steps = {
            step.get("name"): step
            for job in _workflow()["jobs"].values()
            for step in job.get("steps", [])
        }
        for name in UNREADABLE_CONDITIONS:
            assert name in steps, name
            with pytest.raises(SyntaxError):
                evaluate(str(steps[name]["if"]), EVENTS["push of a merge into main"])
