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
spelled.
"""

from __future__ import annotations

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


def _runs_pytest(entry: str) -> list[str] | None:
    """The arguments after `pytest` in a command, or None if it does not
    run pytest."""
    tokens = shlex.split(entry)
    for index, token in enumerate(tokens):
        if token == "pytest" or token.endswith("/pytest"):
            return tokens[index + 1:]
    return None


# ---------------------------------------------------------------------------
# A small evaluator for GitHub Actions expressions: string literals, context
# names, `==` / `!=` (case-insensitive on strings, as Actions compares them),
# `!`, `&&`, `||` and parentheses — what ci.yml's conditions use.  Anything
# else is a SyntaxError, so a condition this cannot read fails the test that
# needed it rather than being skipped.
# ---------------------------------------------------------------------------

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


def evaluate(expr: str, context: dict[str, object]) -> object:
    """Evaluate one expression, with or without its `${{ }}` wrapper."""
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
                raise SyntaxError(f"function call {text}() in {expr!r}")
            if text in ("true", "false"):
                return text == "true"
            return context.get(text)
        raise SyntaxError(f"unexpected {text!r} in {expr!r}")

    def comparison() -> object:
        nonlocal pos
        left = atom()
        token = peek()
        if token in (("op", "=="), ("op", "!=")):
            pos += 1
            right = atom()
            same = equal(left, right)
            return same if token == ("op", "==") else not same
        return left

    def negation() -> object:
        nonlocal pos
        if peek() == ("op", "!"):
            pos += 1
            return not truthy(negation())
        return comparison()

    def conjunction() -> object:
        nonlocal pos
        value = negation()
        while peek() == ("op", "&&"):
            pos += 1
            right = negation()
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
        result = evaluate(m.group(0), context)
        if result is None:
            return ""
        if isinstance(result, bool):
            return "true" if result else "false"
        return str(result)

    return re.sub(r"\$\{\{.*?\}\}", value, command)


def _step_runs(step: dict[str, Any], context: dict[str, object]) -> bool:
    condition = step.get("if")
    if condition is None:
        return True
    return evaluate(str(condition), context) not in (None, False, "", 0)


# The four events the brief of every gate is written against.
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
    },
    "push to release/v0.2.0": {
        "github.event_name": "push",
        "github.base_ref": "",
        "github.ref": "refs/heads/release/v0.2.0",
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
            ("missing", {}, None),
        ],
    )
    def test_it_evaluates(
        self, expr: str, context: dict[str, object], want: object
    ) -> None:
        assert evaluate(expr, context) == want

    @pytest.mark.parametrize("expr", ["contains(a, 'x')", "a ==", "a b", "a > 'x'"])
    def test_what_it_cannot_read_is_an_error(self, expr: str) -> None:
        with pytest.raises(SyntaxError):
            evaluate(expr, {"a": "x"})


# ---------------------------------------------------------------------------
# The local hook: fast gates only
# ---------------------------------------------------------------------------


class TestThePreCommitHookIsFast:
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
        assert len(cells) == 13
        for cell in cells:
            context = {**EVENTS[event], **cell}
            suites = [
                step for step in job["steps"]
                if "run" in step
                and _runs_pytest(step["run"]) is not None
                and _step_runs(step, context)
            ]
            assert len(suites) == 1, (
                f"{cell}: {len(suites)} pytest steps run, not exactly one"
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
        jobs = _workflow()["jobs"]
        context = EVENTS[event]
        for job, script, eager in [
            ("lint", "scripts/check_conformance.py", False),
            ("lint", "scripts/check_examples.py", False),
            ("lint", "scripts/check_examples_run.py", False),
            ("lint", "scripts/check_e602_clean.py", False),
            ("eager-gc", "scripts/check_conformance.py", True),
            ("eager-gc", "scripts/check_examples_run.py", True),
        ]:
            steps = [
                step for step in jobs[job]["steps"]
                if script in step.get("run", "") and _step_runs(step, context)
            ]
            assert len(steps) == 1, f"{job} runs {script} {len(steps)} times"
            if eager:
                assert str(steps[0].get("env", {}).get("VERA_EAGER_GC")) == "1"

    def test_every_gate_the_hook_runs_also_runs_in_ci(self) -> None:
        workflow = _workflow()
        steps = [
            step for job in workflow["jobs"].values() for step in job.get("steps", [])
        ]
        runs = "\n".join(str(step.get("run", "")) for step in steps)
        # The pre-commit-hooks hooks run in CI through pre-commit itself.
        hygiene = "\n".join(
            str(step["run"]) for step in steps
            if "pre-commit run --all-files" in str(step.get("run", ""))
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
            if _runs_pytest(entry) is not None:
                # The staged-files run and the collection are covered by the
                # whole suite (test_every_matrix_cell_runs_the_whole_suite);
                # a named test file must be run by name.
                for arg in _runs_pytest(entry) or []:
                    if arg.startswith("tests/") and arg not in runs:
                        missing.append(f"{hook['id']} ({arg})")
                continue
            script = re.search(r"scripts/\w+\.py", entry)
            if script is not None:
                wanted = CI_COUNTERPART.get(script.group(0), script.group(0))
            else:
                wanted = entry.removeprefix(".venv/bin/")
            if wanted not in runs:
                missing.append(f"{hook['id']} ({wanted})")
        assert missing == [], f"local gates CI does not run: {missing}"

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

    @pytest.mark.parametrize(
        ("event", "release"),
        [
            ("pull request into main", True),
            ("push to main", True),
            ("pull request into release/v0.2.0", False),
            ("push to release/v0.2.0", False),
        ],
    )
    def test_doc_counts_runs_in_release_mode_on_main_only(
        self, event: str, release: bool
    ) -> None:
        steps = [
            step for step in _workflow()["jobs"]["lint"]["steps"]
            if "scripts/check_doc_counts.py" in step.get("run", "")
        ]
        assert len(steps) == 1
        assert _step_runs(steps[0], EVENTS[event])
        argv = shlex.split(render(steps[0]["run"], EVENTS[event]))
        assert argv[:2] == ["python", "scripts/check_doc_counts.py"]
        assert argv[2:] == (["--release"] if release else [])
