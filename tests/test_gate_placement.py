"""Where each gate runs: the fast ones at commit time, every one in CI.

The local pre-commit hook runs the fast gates — lint, types, the doc and
consistency gates, and the test files a commit stages — and CI runs all of
them plus the slow ones: the full pytest suite (the conformance suite is
part of it), the examples' check and verify through the CLI and their runs,
and the E602/E604 compile sweep.  Both halves are read from the configuration files
themselves:

- ``.pre-commit-config.yaml``: no hook runs the whole suite, one of the slow
  sweeps or a count check, and the doc-example hook fires on exactly the
  documents its gate reads.
- ``.github/workflows/ci.yml``: ``pull_request`` and ``push`` reach ``main``
  unfiltered, and a nightly ``schedule`` runs on it.  On a pull request, on
  the push event a merge that raises ``[project].version`` produces (a
  release) and on the nightly run, every matrix cell runs the whole suite:
  on a pull request with each class-instrument matrix sampled, bar the ones
  whose file or deciding module it changes, which the plan job lists
  (tests/matrix_sample.py), and elsewhere with every cell.
  On the push event any other merge produces, the pull request's own run
  has already tested that tree on every cell (strict branch protection), so
  the matrix stands down and the coverage job runs the whole suite once,
  instrumented.  The examples' check, verify and runs and the sweep run on
  every event, every gate the hook runs is run too, and TESTING.md's
  generated status is checked exactly when the version rises.

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
shell control operator, not text it mentions.  The known evasions are pinned
at the end of the file.
"""

from __future__ import annotations

import importlib.util
import itertools
import re
import shlex
import sys
from pathlib import Path
from typing import Any

import pytest

# PyYAML arrives with pre-commit, a `[dev]` dependency that reads its own
# configuration with it, so the files are read here the way pre-commit and
# Actions read them rather than by pattern.
import yaml

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


def _triggers(workflow: dict[Any, Any]) -> dict[str, Any]:
    # YAML 1.1 reads the bare key `on` as the boolean True.
    return dict(workflow.get("on", workflow.get(True)) or {})


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
    workflow's `defaults`; a job that does not run gates nothing.  A run
    command that swallows its own failure (`|| true`, `set +e`, …) fails the
    test outright: its step is not a gate however the job is configured."""
    _can_fail(workflow, context, "the workflow")
    job = workflow["jobs"][job_name]
    if not _runs(job, context, f"job {job_name}"):
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


# The events every gate has to hold on: a pull request into main, the push
# event a merged pull request produces on main (whether or not the merge
# raised `[project].version`, which the plan job answers), and the nightly
# schedule.  `needs.plan.outputs.release` is empty where the plan job's step
# does not run: it reads the version on a push only.  Its other answer,
# `needs.plan.outputs.changed`, is the files a pull request changes that a
# class-instrument matrix can be decided by, and empty on every other event.
_WORKFLOW = {"github.workflow": "CI"}
EVENTS = {
    "pull request into main": {
        **_WORKFLOW,
        "github.event_name": "pull_request",
        "github.base_ref": "main",
        "github.ref": "refs/pull/1/merge",
        "needs.plan.outputs.release": "",
        "needs.plan.outputs.changed": "vera/narrowing.py\ntests/test_one_classifier_1503.py",
    },
    "push of a merge into main": {
        **_WORKFLOW,
        "github.event_name": "push",
        "github.base_ref": "",
        "github.ref": "refs/heads/main",
        "github.event.before": "1" * 40,
        "needs.plan.outputs.release": "false",
        "needs.plan.outputs.changed": "",
    },
    "push of a release merge into main": {
        **_WORKFLOW,
        "github.event_name": "push",
        "github.base_ref": "",
        "github.ref": "refs/heads/main",
        "github.event.before": "2" * 40,
        "needs.plan.outputs.release": "true",
        "needs.plan.outputs.changed": "",
    },
    "nightly schedule": {
        **_WORKFLOW,
        "github.event_name": "schedule",
        "github.base_ref": "",
        "github.ref": "refs/heads/main",
        "github.sha": "3" * 40,
        "needs.plan.outputs.release": "",
        "needs.plan.outputs.changed": "",
    },
}

# Where the whole matrix runs, and where the coverage job runs instead of it.
FULL_MATRIX = (
    "pull request into main",
    "push of a release merge into main",
    "nightly schedule",
)
COVERAGE = ("push of a merge into main", "push of a release merge into main")


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
# CI: everything, on every event, on main
# ---------------------------------------------------------------------------


def _matrix_cells(job: dict[str, Any]) -> list[dict[str, object]]:
    matrix = job["strategy"]["matrix"]
    axes = {k: v for k, v in matrix.items() if k not in ("include", "exclude")}
    cells = [
        {f"matrix.{k}": v for k, v in zip(axes, values, strict=True)}
        for values in itertools.product(*axes.values())
    ]
    assert "exclude" not in matrix, "the cell arithmetic here ignores exclude"
    cells += [
        {f"matrix.{k}": v for k, v in extra.items()}
        for extra in matrix.get("include", [])
    ]
    return cells


# The arguments that do not narrow what the suite runs.  Anything else on a
# CI pytest command must be classified here, deliberately.  `--matrix=full`
# runs every cell of the class-instrument matrices, so it narrows nothing;
# `--matrix=sample` narrows them to their sample whatever changed, and is
# left for the caller to refuse.  A command with no `--matrix` samples them
# too, bar the files `VERA_MATRIX_CHANGED` puts in full, so where that
# default is allowed is `_matrix_mode`'s question, not this one's.
def _narrowing(args: list[str]) -> list[str]:
    out: list[str] = []
    skip_value = False
    for arg in args:
        if skip_value:
            skip_value = False
            continue
        if arg in ("-v", "-vv", "-q"):
            continue
        if arg == "-n":
            skip_value = True
            continue
        if re.fullmatch(r"--cov(-report|-fail-under)?=\S+", arg):
            continue
        if arg == "--matrix=full":
            continue
        out.append(arg)
    return out


def _matrix_mode(args: list[str]) -> str | None:
    """How a pytest command runs the class-instrument matrices
    (tests/matrix_sample.py): `full`, `sample`, or None for the default,
    the sample bar the files the changed-file list puts in full."""
    modes = [arg.split("=", 1)[1] for arg in args if arg.startswith("--matrix=")]
    return modes[-1] if modes else None


class TestCiRunsEveryGate:
    """Each gate runs on each of the modelled events and can fail the run.

    A step counts only where `_gating_steps` says it runs and can fail: its
    job's and its own conditions evaluated for the event (and matrix cell),
    no `continue-on-error`, no shell substituted for `bash -e`, and no run
    command that swallows its own failure."""

    def test_both_events_reach_main_unfiltered(self) -> None:
        triggers = _triggers(_workflow())
        for event in ("push", "pull_request"):
            assert event in triggers, event
            spec = triggers[event] or {}
            assert set(spec.get("branches", [])) == {"main"}, event
            for narrowing in ("paths", "paths-ignore", "branches-ignore"):
                assert narrowing not in spec, (
                    f"{event} carries `{narrowing}`, so some changes would"
                    " reach main without CI"
                )

    def test_the_nightly_run_is_scheduled_once_a_day(self) -> None:
        """The full matrix runs every day whatever merged: a merge that
        keeps the version stands it down (below), so the schedule is what
        still runs every cell on main as it stands."""
        schedule = _triggers(_workflow()).get("schedule") or []
        assert len(schedule) == 1, schedule
        minute, hour, *calendar = str(schedule[0]["cron"]).split()
        assert minute.isdigit() and hour.isdigit(), schedule
        assert calendar == ["*", "*", "*"], f"not daily: {schedule}"

    def test_only_the_matrix_and_the_coverage_job_are_conditional(self) -> None:
        """Every job runs on every event, bar two, and those two are pinned
        to their events: the matrix stands down on the push event a merge
        that keeps the version produces, and the coverage job runs on the
        push event every merge produces, and only there, so no pull request
        waits on an instrumented run."""
        jobs = _workflow()["jobs"]
        for name in ("plan", "test", "coverage", "lint", "eager-gc", "typecheck", "browser-parity"):
            assert name in jobs, name
        for name, job in jobs.items():
            runs_on = {
                event for event, context in EVENTS.items()
                if _runs(job, context, f"job {name}")
            }
            if name == "test":
                assert runs_on == set(FULL_MATRIX), sorted(runs_on)
            elif name == "coverage":
                assert runs_on == set(COVERAGE), sorted(runs_on)
            else:
                assert "if" not in job, f"job {name} has an `if`"

    @pytest.mark.parametrize("event", FULL_MATRIX)
    def test_every_matrix_cell_runs_the_whole_suite(self, event: str) -> None:
        workflow = _workflow()
        job = workflow["jobs"]["test"]
        env = {**workflow.get("env", {}), **job.get("env", {})}
        assert "PYTEST_ADDOPTS" not in env
        cells = _matrix_cells(job)
        for cell in cells:
            steps = _gating_steps(workflow, "test", {**EVENTS[event], **cell})
            suites = [step for step in steps if _runs_pytest(step["run"]) is not None]
            assert len(suites) == 1, (
                f"{cell}: {len(suites)} gating pytest steps, not exactly one"
            )
            step = suites[0]
            assert "PYTEST_ADDOPTS" not in step.get("env", {})
            args = _runs_pytest(step["run"])
            assert args is not None
            assert _narrowing(args) == [], (
                f"{cell}: `{step['run']}` narrows the suite with"
                f" {_narrowing(args)}"
            )
            # The class-instrument matrices (tests/matrix_sample.py): a pull
            # request runs each one's sample, and every cell of one whose
            # file or deciding module it changes, from the plan job's list;
            # the release push and the nightly run run every cell.
            pull_request = EVENTS[event]["github.event_name"] == "pull_request"
            want = None if pull_request else "full"
            assert _matrix_mode(args) == want, (
                f"{cell}: `{step['run']}` runs the matrices"
                f" {_matrix_mode(args) or 'by default'}, not {want or 'by default'}"
            )
            if pull_request:
                assert (step.get("env") or {}).get("VERA_MATRIX_CHANGED") == (
                    "${{ needs.plan.outputs.changed }}"
                ), f"{cell}: the suite is not handed the plan job's list of changed files"
            # Instrumentation costs a cell about 2.5x; the coverage job pays
            # it, after the merge, so no cell of the matrix does (#1624).
            assert not any(arg.startswith("--cov") for arg in args), (
                f"{cell}: `{step['run']}` measures coverage in the matrix"
            )

    def test_the_push_of_a_merge_runs_the_whole_suite_once_with_coverage(self) -> None:
        """Under strict branch protection a pull request's last run tested
        the tree its merge produces, on every cell, so the push event that
        merge produces runs no cell of the matrix.  It runs the whole suite
        once, in the coverage job: instrumented with the sysmon core on
        ubuntu-latest and Python 3.12, which is what keeps Codecov tracking
        main."""
        workflow = _workflow()
        context = EVENTS["push of a merge into main"]
        for cell in _matrix_cells(workflow["jobs"]["test"]):
            assert _gating_steps(workflow, "test", {**context, **cell}) == [], cell
        job = workflow["jobs"]["coverage"]
        assert "strategy" not in job
        assert job["runs-on"] == "ubuntu-latest"
        steps = _gating_steps(workflow, "coverage", context)
        pythons = [
            str(step["with"]["python-version"]) for step in steps
            if str(step.get("uses", "")).startswith("actions/setup-python@")
        ]
        assert pythons == ["3.12"], pythons
        suites = [step for step in steps if _runs_pytest(step["run"]) is not None]
        assert len(suites) == 1, f"{len(suites)} gating pytest steps, not exactly one"
        step = suites[0]
        args = _runs_pytest(step["run"])
        assert args is not None
        assert _narrowing(args) == [], (
            f"`{step['run']}` narrows the suite with {_narrowing(args)}"
        )
        assert "--cov=vera" in args, args
        assert any(arg.startswith("--cov-fail-under=") for arg in args), args
        # Every cell of the class-instrument matrices: the push event of a
        # merge that keeps the version runs no matrix cell, so this run is
        # the one place their every cell runs before the nightly.
        assert _matrix_mode(args) == "full", args
        assert step.get("env", {}).get("COVERAGE_CORE") == "sysmon"
        assert any(
            str(step.get("uses", "")).startswith("codecov/codecov-action@")
            for step in steps
        ), "the coverage job uploads nothing"

    def test_the_plan_reads_the_version_bump_on_a_push(self) -> None:
        """The matrix waits for the plan job, whose first answer is whether
        a push raised `[project].version`: the release-mode rule of
        check_doc_counts.py (#1536), asked of the commit before the push and
        written to the step's outputs.  On any other event the step does not
        run and the matrix does not ask.  Its second answer, the files a
        pull request changes, is the test below."""
        workflow = _workflow()
        jobs = workflow["jobs"]
        assert "plan" in jobs, "no plan job"
        assert jobs["test"].get("needs") in ("plan", ["plan"])
        outputs = jobs["plan"].get("outputs") or {}
        assert set(outputs) == {"release", "changed"}, outputs
        m = re.fullmatch(
            r"\$\{\{\s*steps\.([\w-]+)\.outputs\.release\s*\}\}",
            str(outputs["release"]),
        )
        assert m is not None, outputs["release"]
        for event, context in EVENTS.items():
            steps = _gating_steps(workflow, "plan", context)
            answers = [step for step in steps if step.get("id") == m.group(1)]
            if context["github.event_name"] != "push":
                assert answers == [], event
                continue
            assert len(answers) == 1, event
            assert _command(answers[0]["run"].strip()) == [
                "python", "scripts/check_doc_counts.py", "--print-release-mode",
                str(context["github.event.before"]), ">>", "$GITHUB_OUTPUT",
            ], answers[0]["run"]
            checkouts = [
                step for step in steps
                if str(step.get("uses", "")).startswith("actions/checkout@")
            ]
            assert len(checkouts) == 1, event
            assert (checkouts[0].get("with") or {}).get("fetch-depth") == 0, (
                "the commit before the push must be in the checkout"
            )

    def test_the_plan_lists_what_a_pull_request_changes(self) -> None:
        """The plan job's second answer, for the class-instrument matrices
        (tests/matrix_sample.py): on a pull request, the files it changes
        that a matrix can be decided by, one per line, which the matrix hands
        the suite as `VERA_MATRIX_CHANGED`.  The range is the pull request's
        own, from its merge base to its head (three dots: what it changes,
        not what `main` has gained since it branched), over a checkout that
        holds both ends; the pathspec keeps the list to the compiler and the
        test files; and the value is written between `changed<<` and a
        random delimiter, so no file name can end it early.  On any other
        event the step does not run and the list is empty."""
        workflow = _workflow()
        outputs = workflow["jobs"]["plan"].get("outputs") or {}
        m = re.fullmatch(
            r"\$\{\{\s*steps\.([\w-]+)\.outputs\.changed\s*\}\}", str(outputs.get("changed")),
        )
        assert m is not None, outputs
        for event, context in EVENTS.items():
            steps = _gating_steps(workflow, "plan", context)
            answers = [step for step in steps if step.get("id") == m.group(1)]
            if context["github.event_name"] != "pull_request":
                assert answers == [], event
                continue
            assert len(answers) == 1, event
            step = answers[0]
            env = step.get("env") or {}
            assert env.get("BASE_SHA") == "${{ github.event.pull_request.base.sha }}", env
            assert env.get("HEAD_SHA") == "${{ github.event.pull_request.head.sha }}", env
            lines = [line.strip() for line in step["run"].splitlines() if line.strip()]
            assert len(lines) == 4, lines
            assignment, opening, diff, closing = lines
            name = re.fullmatch(r'(\w+)="changed_\$\(openssl rand -hex (\d+)\)"', assignment)
            assert name is not None and int(name.group(2)) >= 16, assignment
            assert _command(opening) == ["echo", f"changed<<${name.group(1)}", ">>", "$GITHUB_OUTPUT"], opening
            assert _command(diff) == [
                "git", "diff", "--name-only", "$BASE_SHA...$HEAD_SHA", "--", "vera/", "tests/test_*.py",
                ">>", "$GITHUB_OUTPUT",
            ], diff
            assert _command(closing) == ["echo", f"${name.group(1)}", ">>", "$GITHUB_OUTPUT"], closing
            checkouts = [
                step for step in steps
                if str(step.get("uses", "")).startswith("actions/checkout@")
            ]
            assert len(checkouts) == 1, event
            assert (checkouts[0].get("with") or {}).get("fetch-depth") == 0, (
                "the pull request's merge base must be in the checkout"
            )

    def test_the_nightly_run_never_holds_a_merge_pending(self) -> None:
        """A run queued in a busy concurrency group waits, and a newer one
        replaces it (GitHub's concurrency rules), so the nightly run has a
        group of its own.  Pull request runs cancel their predecessors; no
        other run is cancelled."""
        concurrency = _workflow()["concurrency"]
        groups = {
            event: render(str(concurrency["group"]), context)
            for event, context in EVENTS.items()
        }
        merges = {groups[event] for event in COVERAGE}
        assert len(merges) == 1, groups
        assert groups["nightly schedule"] not in merges, groups
        for event, context in EVENTS.items():
            cancels = _truthy(evaluate(str(concurrency["cancel-in-progress"]), context))
            assert cancels == (context["github.event_name"] == "pull_request"), event

    @pytest.mark.parametrize("event", sorted(EVENTS))
    def test_conformance_and_the_examples_run(self, event: str) -> None:
        """The conformance programs are part of the whole suite
        (tests/test_conformance.py), which the tests above run on every
        event.  The examples' check and verify through the CLI (the suite's
        example tests call the checker and verifier in-process), their runs
        and the compile sweep run here on every event, and the runs again
        under VERA_EAGER_GC=1: the conformance programs through the suite's
        own run stage, since a collection changes no other stage."""
        workflow = _workflow()
        context = EVENTS[event]
        for job, script, eager in [
            ("lint", "scripts/check_examples.py", False),
            ("lint", "scripts/check_examples_run.py", False),
            ("lint", "scripts/check_e602_clean.py", False),
            ("eager-gc", "scripts/check_examples_run.py", True),
        ]:
            steps = _invokes(_gating_steps(workflow, job, context), "python", script)
            assert len(steps) == 1, f"{job} runs {script} {len(steps)} times"
            if eager:
                assert str(steps[0].get("env", {}).get("VERA_EAGER_GC")) == "1"
        runs = _invokes(
            _gating_steps(workflow, "eager-gc", context),
            "pytest", "tests/test_conformance.py", "-k", "run",
        )
        assert len(runs) == 1, f"eager-gc runs the conformance runs {len(runs)} times"
        assert str(runs[0].get("env", {}).get("VERA_EAGER_GC")) == "1"

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
                # The staged-files run and the collection are covered by the
                # whole suite (test_every_matrix_cell_runs_the_whole_suite);
                # a named test file must be run by name.
                for arg in args:
                    if arg.startswith("tests/") and not any(
                        arg in (_runs_pytest(step["run"]) or []) for step in steps
                    ):
                        missing.append(f"{hook['id']} ({arg})")
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

    @pytest.mark.parametrize(
        ("event", "base"),
        [
            ("pull request into main", "main"),
            ("push of a merge into main", "1" * 40),
            ("push of a release merge into main", "2" * 40),
            ("nightly schedule", "3" * 40),
        ],
    )
    def test_doc_counts_keys_release_mode_on_the_version_bump(
        self, event: str, base: str
    ) -> None:
        """Release mode is chosen by the script from the version bump
        (#1536), never by the event: a pull request hands it its base
        branch, a push the commit before it, and the nightly run, which has
        no commit before it, the commit it tests, which raises nothing.  A
        base branch alone named the release PR only while fix PRs targeted
        a release branch."""
        steps = _invokes(
            _gating_steps(_workflow(), "lint", EVENTS[event]),
            "python", "scripts/check_doc_counts.py",
        )
        assert len(steps) == 1
        argv = _command(steps[0]["run"])
        assert argv[2:] == ["--release-if-version-raised", base]


# ---------------------------------------------------------------------------
# The known evasions, pinned.  Each is an edit to one configuration file that
# stops a gate running or stops it failing the run while leaving its text in
# place; each must turn the named check red.  The edits are applied to copies
# in memory, never to the files on disk.
# ---------------------------------------------------------------------------

_SWEEP = (
    "      - name: Check no unexpected [E602]/[E604] silent skips (Layer 1 of #626)\n"
    "        run: python scripts/check_e602_clean.py\n"
)
_WALK = (
    "      - name: Check every walker covers every Expr subclass (#597)\n"
    "        run: python scripts/check_walker_coverage.py\n"
)
_STAGED = "        files: '^tests/test_[^/]*\\.py$'\n        require_serial: true\n"


def _walk_if(condition: str) -> str:
    return _WALK.replace("        run:", f"        if: {condition}\n        run:", 1)


def _sweep_run(run: str) -> str:
    return _SWEEP.replace("python scripts/check_e602_clean.py", run, 1)


# The matrix's condition and the coverage job's, as ci.yml spells them.
_MATRIX_IF = "    if: github.event_name != 'push' || needs.plan.outputs.release == 'true'\n"
_COVERAGE_IF = "  coverage:\n    if: github.event_name == 'push'\n"

# The matrix's test step and the plan job's list, as ci.yml spells them.
_MATRIX_FLAG = "${{ github.event_name != 'pull_request' && '--matrix=full' || '' }}"
_CHANGED_ENV = "        env:\n          VERA_MATRIX_CHANGED: ${{ needs.plan.outputs.changed }}\n"
_CHANGED_IF = "        id: changed\n        if: github.event_name == 'pull_request'\n"
_CHANGED_DIFF = "git diff --name-only \"$BASE_SHA...$HEAD_SHA\" -- vera/ 'tests/test_*.py'"
_COVERAGE_RUN = "--cov-fail-under=80 --matrix=full\n"

_COUNTERPART = ("counterpart", "pull request into main")
_SWEEPS = ("sweeps", "pull request into main")
_WHOLE_SUITE = ("whole suite", None)
_PR_MATRIX = ("matrix", "pull request into main")
_NIGHTLY_MATRIX = ("matrix", "nightly schedule")
_RELEASE_MATRIX = ("matrix", "push of a release merge into main")
_CONDITIONAL = ("conditional", None)
_COVERAGE = ("coverage", None)
_PLAN = ("plan", None)

EVASIONS = [
    ("walker coverage on push only", CI, _WALK, _walk_if("github.event_name == 'push'"), _COUNTERPART),
    ("sweep step continue-on-error", CI, _SWEEP,
     _SWEEP.replace("        run:", "        continue-on-error: true\n        run:", 1), _SWEEPS),
    ("staged-test hook always_run", PRECOMMIT, _STAGED, _STAGED + "        always_run: true\n", _WHOLE_SUITE),
    ("eager-gc job continue-on-error", CI, "  eager-gc:\n", "  eager-gc:\n    continue-on-error: true\n", _SWEEPS),
    ("sweep piped to tee", CI, _SWEEP, _sweep_run("python scripts/check_e602_clean.py | tee sweep.log"), _SWEEPS),
    ("sweep backgrounded", CI, _SWEEP, _sweep_run("python scripts/check_e602_clean.py &"), _SWEEPS),
    ("sweep in an and-list, not last", CI, _SWEEP,
     "      - name: Check no unexpected [E602]/[E604] silent skips (Layer 1 of #626)\n"
     "        run: |\n"
     "          python scripts/check_e602_clean.py && echo sweep ok\n"
     "          echo done\n", _SWEEPS),
    ("sweep in an and-list on one line", CI, _SWEEP,
     _sweep_run("python scripts/check_e602_clean.py && echo sweep ok; echo done"), _SWEEPS),
    ("walker coverage piped to tee", CI, _WALK,
     _WALK.replace("check_walker_coverage.py", "check_walker_coverage.py | tee walker.log", 1), _COUNTERPART),
    ("walker coverage behind an unmodelled head_ref", CI, _WALK, _walk_if("github.head_ref != ''"), _COUNTERPART),
    ("sweep skipped for an unmodelled actor", CI, _SWEEP,
     _SWEEP.replace("        run:", "        if: github.actor != 'dependabot[bot]'\n        run:", 1), _SWEEPS),
    ("sweep may fail for an unmodelled actor", CI, _SWEEP,
     _SWEEP.replace(
         "        run:",
         "        continue-on-error: ${{ github.actor == 'dependabot[bot]' }}\n        run:", 1,
     ), _SWEEPS),
    ("walker coverage behind a precedence trap", CI, _WALK,
     _walk_if("${{ !github.event_name == 'schedule' }}"), _COUNTERPART),
    ("staged-test hook as python -m pytest over tests/", PRECOMMIT,
     "        entry: .venv/bin/pytest -q -n 4 --matrix=full\n",
     "        entry: .venv/bin/python -m pytest tests/ -q --matrix=full\n",
     _WHOLE_SUITE),
    ("matrix gated on the plan alone, so a pull request runs no cell", CI, _MATRIX_IF,
     "    if: needs.plan.outputs.release == 'true'\n", _PR_MATRIX),
    ("matrix on pull requests and releases only, so the nightly runs no cell", CI, _MATRIX_IF,
     "    if: github.event_name == 'pull_request' || needs.plan.outputs.release == 'true'\n",
     _NIGHTLY_MATRIX),
    ("coverage job on every event, so a pull request waits on it", CI, _COVERAGE_IF,
     "  coverage:\n", _CONDITIONAL),
    ("pull request held to the matrices' sample, so a changed decider runs no more", CI, _MATRIX_FLAG,
     "--matrix=${{ github.event_name == 'pull_request' && 'sample' || 'full' }}", _PR_MATRIX),
    ("changed-file list never handed to the suite", CI, _CHANGED_ENV, "", _PR_MATRIX),
    ("nightly run left to the default sample", CI, _MATRIX_FLAG,
     "${{ github.event_name == 'push' && '--matrix=full' || '' }}", _NIGHTLY_MATRIX),
    ("release push left to the default sample", CI, _MATRIX_FLAG,
     "${{ github.event_name == 'schedule' && '--matrix=full' || '' }}", _RELEASE_MATRIX),
    ("coverage job sampled", CI, _COVERAGE_RUN, "--cov-fail-under=80\n", _COVERAGE),
    ("changed-file list made on a push only", CI, _CHANGED_IF,
     "        id: changed\n        if: github.event_name == 'push'\n", _PLAN),
    ("changed files diffed from main's tip, not the merge base", CI, _CHANGED_DIFF,
     _CHANGED_DIFF.replace("...", "..", 1), _PLAN),
    ("changed files listed without a pathspec", CI, _CHANGED_DIFF,
     _CHANGED_DIFF.split(" -- ", 1)[0], _PLAN),
]


@pytest.mark.parametrize(
    ("path", "old", "new", "check"),
    [pytest.param(path, old, new, check, id=name) for name, path, old, new, check in EVASIONS],
)
def test_each_known_evasion_is_caught(
    monkeypatch: pytest.MonkeyPatch, path: Path, old: str, new: str, check: tuple[str, str | None]
) -> None:
    text = path.read_text(encoding="utf-8")
    assert text.count(old) == 1, f"the evasion's anchor moved in {path.name}"
    edited = yaml.safe_load(text.replace(old, new, 1))
    module = sys.modules[__name__]
    if path == CI:
        monkeypatch.setattr(module, "_workflow", lambda: dict(edited))
    else:
        monkeypatch.setattr(module, "_hooks", lambda: [
            {**hook, "repo": repo["repo"]} for repo in edited["repos"] for hook in repo["hooks"]
        ])
    kind, event = check
    with pytest.raises((AssertionError, pytest.fail.Exception)):
        if kind == "counterpart":
            TestCiRunsEveryGate().test_every_gate_the_hook_runs_also_runs_in_ci(str(event))
        elif kind == "sweeps":
            TestCiRunsEveryGate().test_conformance_and_the_examples_run(str(event))
        elif kind == "matrix":
            TestCiRunsEveryGate().test_every_matrix_cell_runs_the_whole_suite(str(event))
        elif kind == "conditional":
            TestCiRunsEveryGate().test_only_the_matrix_and_the_coverage_job_are_conditional()
        elif kind == "coverage":
            TestCiRunsEveryGate().test_the_push_of_a_merge_runs_the_whole_suite_once_with_coverage()
        elif kind == "plan":
            TestCiRunsEveryGate().test_the_plan_lists_what_a_pull_request_changes()
        else:
            TestThePreCommitHookIsFast().test_no_hook_runs_the_whole_suite()
