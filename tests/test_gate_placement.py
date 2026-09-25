"""Where each gate runs: the fast ones at commit time, every one in CI.

The local pre-commit hook runs the fast gates — lint, types, the doc and
consistency gates, and the test files a commit stages — and CI runs all of
them plus the slow ones: the full pytest suite on every cell of the test
matrix, the conformance suite, and the examples.  Both halves are read from
the configuration files themselves:

- ``.pre-commit-config.yaml``: the hook set is the pinned list, and no hook
  runs the whole suite or one of the slow sweeps.
- ``.github/workflows/ci.yml``: on both ``pull_request`` and ``push`` to
  ``main`` and ``release/**``, every matrix cell runs the whole suite,
  conformance and the examples run, every gate the hook runs is run too,
  and the documentation counts run in release mode exactly on ``main``.

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

# The hook set, in order.  A change to it is a decision about what a commit
# costs, and belongs in this list and in TESTING.md's hook table together.
COMMIT_STAGE = (
    "trailing-whitespace",
    "end-of-file-fixer",
    "check-yaml",
    "check-toml",
    "check-merge-conflict",
    "check-added-large-files",
    "debug-statements",
    "ruff",
    "ruff-security",
    "mypy",
    "pytest-staged",
    "pytest-collect",
    "corpus-canonical",
    "examples-readme",
    "doc-examples",
    "diagnostic-examples",
    "doc-builtin-shadowing",
    "grammar-alignment",
    "editor-grammars",
    "doc-counts",
    "walker-coverage",
    "diagnostic-fields",
    "explicit-encoding",
    "limitations-sync",
    "license-check",
    "version-sync",
    "site-assets",
    "site-assets-check",
    "browser-parity",
)
PUSH_STAGE = ("check-changelog-updated", "uv-lock-check")

# The gates that are too slow for a commit and run in CI only.
CI_ONLY_SCRIPTS = (
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


# The four events every gate has to hold on.
EVENTS = {
    "pull request into main": {
        "github.event_name": "pull_request",
        "github.base_ref": "main",
        "github.ref": "refs/pull/1/merge",
    },
    "pull request into release/v0.2.0": {
        "github.event_name": "pull_request",
        "github.base_ref": "release/v0.2.0",
        "github.ref": "refs/pull/1/merge",
    },
    "push to main": {
        "github.event_name": "push",
        "github.base_ref": "",
        "github.ref": "refs/heads/main",
        "github.event.before": "1" * 40,
    },
    "push to release/v0.2.0": {
        "github.event_name": "push",
        "github.base_ref": "",
        "github.ref": "refs/heads/release/v0.2.0",
        "github.event.before": "2" * 40,
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

    def test_the_hook_set_is_pinned(self) -> None:
        hooks = _hooks()
        assert [hook["id"] for hook in hooks] == [*COMMIT_STAGE, *PUSH_STAGE]
        for hook in hooks:
            stages = hook.get("stages")
            if hook["id"] in PUSH_STAGE:
                assert stages == ["pre-push"], hook["id"]
            else:
                assert stages is None, hook["id"]

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
            for script in CI_ONLY_SCRIPTS:
                assert script not in entry, (
                    f"{hook['id']} runs {script}, which runs in CI only"
                )

    @pytest.mark.parametrize(
        ("hook_id", "command"),
        [
            ("ruff", "ruff check ."),
            ("ruff-security", "ruff check --select S vera/"),
            ("mypy", "mypy vera/"),
            ("doc-counts", "scripts/check_doc_counts.py"),
            ("site-assets", "scripts/build_site.py"),
            ("site-assets-check", "scripts/check_site_assets.py"),
            ("explicit-encoding", "scripts/check_explicit_encoding.py"),
            ("version-sync", "scripts/check_version_sync.py"),
            ("limitations-sync", "scripts/check_limitations_sync.py"),
            ("diagnostic-fields", "scripts/check_diagnostic_fields.py"),
            ("doc-examples", "scripts/check_doc_examples.py"),
            ("check-changelog-updated", "scripts/check_changelog_updated.py"),
        ],
    )
    def test_each_fast_gate_runs_its_command(self, hook_id: str, command: str) -> None:
        hook = next(h for h in _hooks() if h["id"] == hook_id)
        assert hook["entry"].endswith(command), hook["entry"]

    def test_the_hook_checks_doc_counts_in_the_default_mode(self) -> None:
        """A commit on a fix branch must not be asked to set the headline
        totals: the release PR does."""
        hook = next(h for h in _hooks() if h["id"] == "doc-counts")
        assert "--release" not in hook["entry"]


# ---------------------------------------------------------------------------
# CI: everything, on both events, on main and release/**
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
# CI pytest command must be classified here, deliberately.
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
        out.append(arg)
    return out


class TestCiRunsEveryGate:
    """Each gate runs on each of the four events and can fail the run.

    A step counts only where `_gating_steps` says it runs and can fail: its
    job's and its own conditions evaluated for the event (and matrix cell),
    no `continue-on-error`, no shell substituted for `bash -e`, and no run
    command that swallows its own failure."""

    def test_both_events_reach_main_and_release_branches_unfiltered(self) -> None:
        triggers = _triggers(_workflow())
        for event in ("push", "pull_request"):
            assert event in triggers, event
            spec = triggers[event] or {}
            assert {"main", "release/**"} <= set(spec.get("branches", [])), event
            for narrowing in ("paths", "paths-ignore", "branches-ignore"):
                assert narrowing not in spec, (
                    f"{event} carries `{narrowing}`, so some changes would"
                    " reach main without CI"
                )

    def test_no_gating_job_is_conditional(self) -> None:
        jobs = _workflow()["jobs"]
        for name in ("test", "lint", "eager-gc", "typecheck", "browser-parity"):
            assert name in jobs, name
            assert "if" not in jobs[name], f"job {name} has an `if`"

    @pytest.mark.parametrize("event", sorted(EVENTS))
    def test_every_matrix_cell_runs_the_whole_suite(self, event: str) -> None:
        workflow = _workflow()
        job = workflow["jobs"]["test"]
        env = {**workflow.get("env", {}), **job.get("env", {})}
        assert "PYTEST_ADDOPTS" not in env
        cells = _matrix_cells(job)
        assert len(cells) == 13, "the matrix is pinned at 13 cells; update with it"
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

    @pytest.mark.parametrize("event", sorted(EVENTS))
    def test_conformance_and_the_examples_run(self, event: str) -> None:
        workflow = _workflow()
        context = EVENTS[event]
        for job, script, eager in [
            ("lint", "scripts/check_conformance.py", False),
            ("lint", "scripts/check_examples.py", False),
            ("lint", "scripts/check_examples_run.py", False),
            ("lint", "scripts/check_e602_clean.py", False),
            ("eager-gc", "scripts/check_conformance.py", True),
            ("eager-gc", "scripts/check_examples_run.py", True),
        ]:
            steps = _invokes(_gating_steps(workflow, job, context), "python", script)
            assert len(steps) == 1, f"{job} runs {script} {len(steps)} times"
            if eager:
                assert str(steps[0].get("env", {}).get("VERA_EAGER_GC")) == "1"

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
                evaluate(str(steps[name]["if"]), EVENTS["push to main"])

    @pytest.mark.parametrize(
        ("event", "base"),
        [
            ("pull request into main", "main"),
            ("pull request into release/v0.2.0", "release/v0.2.0"),
            ("push to main", "1" * 40),
            ("push to release/v0.2.0", "2" * 40),
        ],
    )
    def test_doc_counts_keys_release_mode_on_the_version_bump(
        self, event: str, base: str
    ) -> None:
        """Release mode is chosen by the script from the version bump
        (#1536), never by the event: a pull request hands it its base
        branch, a push the commit before it.  A base branch alone named
        the release PR only while fix PRs targeted a release branch."""
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

_CONF = "      - name: Check conformance suite\n        run: python scripts/check_conformance.py\n"
_WALK = (
    "      - name: Check every walker covers every Expr subclass (#597)\n"
    "        run: python scripts/check_walker_coverage.py\n"
)
_STAGED = "        files: '^tests/test_[^/]*\\.py$'\n        require_serial: true\n"


def _walk_if(condition: str) -> str:
    return _WALK.replace("        run:", f"        if: {condition}\n        run:", 1)


def _conf_run(run: str) -> str:
    return _CONF.replace("python scripts/check_conformance.py", run, 1)


_COUNTERPART = ("counterpart", "pull request into release/v0.2.0")
_CONFORMANCE = ("conformance", "pull request into release/v0.2.0")
_WHOLE_SUITE = ("whole suite", None)

EVASIONS = [
    ("walker coverage on push only", CI, _WALK, _walk_if("github.event_name == 'push'"), _COUNTERPART),
    ("conformance step continue-on-error", CI, _CONF,
     _CONF.replace("        run:", "        continue-on-error: true\n        run:", 1), _CONFORMANCE),
    ("staged-test hook always_run", PRECOMMIT, _STAGED, _STAGED + "        always_run: true\n", _WHOLE_SUITE),
    ("eager-gc job continue-on-error", CI, "  eager-gc:\n", "  eager-gc:\n    continue-on-error: true\n", _CONFORMANCE),
    ("conformance piped to tee", CI, _CONF, _conf_run("python scripts/check_conformance.py | tee conformance.log"), _CONFORMANCE),
    ("conformance backgrounded", CI, _CONF, _conf_run("python scripts/check_conformance.py &"), _CONFORMANCE),
    ("conformance in an and-list, not last", CI, _CONF,
     "      - name: Check conformance suite\n        run: |\n"
     "          python scripts/check_conformance.py && echo conformance ok\n"
     "          echo done\n", _CONFORMANCE),
    ("conformance in an and-list on one line", CI, _CONF,
     _conf_run("python scripts/check_conformance.py && echo conformance ok; echo done"), _CONFORMANCE),
    ("walker coverage piped to tee", CI, _WALK,
     _WALK.replace("check_walker_coverage.py", "check_walker_coverage.py | tee walker.log", 1), _COUNTERPART),
    ("walker coverage behind an unmodelled head_ref", CI, _WALK, _walk_if("github.head_ref != ''"), _COUNTERPART),
    ("conformance skipped for an unmodelled actor", CI, _CONF,
     _CONF.replace("        run:", "        if: github.actor != 'dependabot[bot]'\n        run:", 1), _CONFORMANCE),
    ("conformance may fail for an unmodelled actor", CI, _CONF,
     _CONF.replace(
         "        run:",
         "        continue-on-error: ${{ github.actor == 'dependabot[bot]' }}\n        run:", 1,
     ), _CONFORMANCE),
    ("walker coverage behind a precedence trap", CI, _WALK,
     _walk_if("${{ !github.event_name == 'schedule' }}"), _COUNTERPART),
    ("staged-test hook as python -m pytest over tests/", PRECOMMIT,
     "        entry: .venv/bin/pytest -q -n 4\n", "        entry: .venv/bin/python -m pytest tests/ -q\n",
     _WHOLE_SUITE),
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
        elif kind == "conformance":
            TestCiRunsEveryGate().test_conformance_and_the_examples_run(str(event))
        else:
            TestThePreCommitHookIsFast().test_no_hook_runs_the_whole_suite()
