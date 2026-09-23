"""Tests for the ``<DB>`` host binding (#229, S3) — ``vera/runtime/db.py``.

The DB effect's host functions execute SQL against the standard-library
``sqlite3`` module and marshal results back through the S2 helpers.  These drive
the impls directly against an in-memory database — create / insert / select
round-trips, ``NULL`` cells, the affected-row count, parameter binding, and the
error path (an ``Err`` value, never a crash).  The end-to-end path through
codegen routing and a real Vera program lands in S4.

``_open_connection`` is also covered: the ``VERA_DB_URL`` config surface and the
hermetic ``sqlite::memory:`` default.
"""
from __future__ import annotations

import sqlite3
from pathlib import Path

import pytest

from vera.codegen import execute
from vera.runtime.db import _db_execute, _db_query, _open_connection
from vera.runtime.heap import _read_i32, _read_wasm_string

from tests.codegen_helpers import _compile_ok, _run

# Reuse the S2 InstanceCaller harness + the row-grid decoder (helpers, not
# tests — the ``test_``-prefix collection rule leaves them alone).
from tests.test_db_marshalling import _decode_result_ok_rows, _gc_caller

# Repo-relative example + committed fixture, resolved from this file's location
# so the test is cwd-independent.
_EXAMPLES = Path(__file__).resolve().parent.parent / "examples"


def _decode_result_ok_i64(caller, adt_ptr: int) -> int:
    assert _read_i32(caller, adt_ptr) == 0, "expected Ok tag"
    lo = _read_i32(caller, adt_ptr + 8)
    hi = _read_i32(caller, adt_ptr + 12)
    got = (hi << 32) | lo
    return got - 2 ** 64 if got >= 2 ** 63 else got


def _decode_result_err(caller, adt_ptr: int) -> str:
    assert _read_i32(caller, adt_ptr) == 1, "expected Err tag"
    s_ptr = _read_i32(caller, adt_ptr + 4)
    s_len = _read_i32(caller, adt_ptr + 8)
    return _read_wasm_string(caller, s_ptr, s_len)


class TestDbRuntime229:
    def test_create_insert_select_roundtrip(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        _db_execute(caller, conn, "CREATE TABLE t (id INTEGER, name TEXT)", [])
        _db_execute(caller, conn, "INSERT INTO t VALUES (?, ?)", ["1", "alice"])
        _db_execute(caller, conn, "INSERT INTO t VALUES (?, ?)", ["2", None])
        result = _db_query(caller, conn, "SELECT id, name FROM t ORDER BY id", [])
        # id is an INTEGER column: "1" is stored/returned as 1 and stringified;
        # the NULL name comes back as None (not "").
        assert _decode_result_ok_rows(caller, result) == [
            ["1", "alice"], ["2", None],
        ]

    def test_parameterised_where_binds_safely(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        _db_execute(caller, conn, "CREATE TABLE u (name TEXT)", [])
        for n in ("alice", "bob", "eve"):
            _db_execute(caller, conn, "INSERT INTO u VALUES (?)", [n])
        # A param that looks like an injection is bound as a literal value, so
        # it matches nothing rather than altering the query.
        result = _db_query(
            caller, conn, "SELECT name FROM u WHERE name = ?", ["bob'; DROP TABLE u--"],
        )
        assert _decode_result_ok_rows(caller, result) == []
        # ... and the table is intact.
        still = _db_query(caller, conn, "SELECT name FROM u ORDER BY name", [])
        assert _decode_result_ok_rows(caller, still) == [["alice"], ["bob"], ["eve"]]

    def test_execute_returns_rowcount(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        _db_execute(caller, conn, "CREATE TABLE t (n INTEGER)", [])
        for i in range(3):
            _db_execute(caller, conn, "INSERT INTO t VALUES (?)", [str(i)])
        deleted = _db_execute(caller, conn, "DELETE FROM t WHERE n >= ?", ["1"])
        assert _decode_result_ok_i64(caller, deleted) == 2  # rows 1 and 2

    def test_query_error_is_err_not_crash(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        result = _db_query(caller, conn, "SELECT * FROM nonexistent", [])
        msg = _decode_result_err(caller, result)
        assert "nonexistent" in msg.lower() or "no such table" in msg.lower()

    def test_execute_error_is_err_not_crash(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        result = _db_execute(caller, conn, "NOT VALID SQL", [])
        assert _read_i32(caller, result) == 1  # Err tag

    def test_multi_statement_sql_is_err_not_a_raised_warning(self) -> None:
        # sqlite3 refuses multiple statements in one `execute` — raising
        # `sqlite3.ProgrammingError` on current Python and `sqlite3.Warning`
        # on some versions.  `Warning` is NOT a subclass of `Error` (they are
        # DB-API siblings), so the handler catches both; either way a
        # semicolon-joined CREATE + INSERT must surface as `Result.Err`, not
        # escape the host callback as an uncaught exception.
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        result = _db_execute(
            caller, conn,
            "CREATE TABLE t (n INTEGER); INSERT INTO t VALUES (1)", [],
        )
        # Reaching this assert at all means no exception escaped.
        assert _read_i32(caller, result) == 1  # Err tag

    def test_open_connection_defaults_to_memory(self) -> None:
        # No VERA_DB_URL → a hermetic in-memory database (no config needed).
        conn = _open_connection({})
        assert isinstance(conn, sqlite3.Connection)
        conn.execute("CREATE TABLE t (x)")  # usable

    @pytest.mark.parametrize("url", ["sqlite::memory:", ":memory:", "sqlite://:memory:"])
    def test_open_connection_memory_urls(self, url: str) -> None:
        conn = _open_connection({"VERA_DB_URL": url})
        assert isinstance(conn, sqlite3.Connection)

    def test_open_connection_file_url(self, tmp_path) -> None:
        db_path = tmp_path / "t.db"
        conn = _open_connection({"VERA_DB_URL": f"sqlite:///{db_path.as_posix()}"})
        conn.execute("CREATE TABLE t (x)")
        conn.commit()
        assert db_path.exists()

    def test_register_db_noop_when_unused(self) -> None:
        # No DB op in the program → nothing bound, no connection opened.
        import wasmtime

        from vera.runtime.db import register_db
        linker = wasmtime.Linker(wasmtime.Engine())
        register_db(linker, set(), {})  # must not raise

    def test_register_db_binds_requested_ops(self) -> None:
        # Binding succeeds (opens the connection, defines the host funcs); the
        # end-to-end link against a compiled module lands in S4.
        import wasmtime

        from vera.runtime.db import register_db
        linker = wasmtime.Linker(wasmtime.Engine())
        register_db(
            linker, {"db_query", "db_execute"},
            {"VERA_DB_URL": "sqlite::memory:"},
        )

    def test_create_table_rowcount_is_minus_one(self) -> None:
        # A statement sqlite cannot count (DDL like CREATE TABLE) reports
        # rowcount -1; the documented sentinel must survive marshalling as a
        # signed i64, not clamp to 0 or turn into lastrowid.
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        result = _db_execute(caller, conn, "CREATE TABLE t (n INTEGER)", [])
        assert _decode_result_ok_i64(caller, result) == -1

    def test_blob_column_decodes_via_utf8_replace(self) -> None:
        # A BLOB cell is bytes, not str: `_cell` UTF-8-decodes it with
        # replacement (not `str(bytes)`, which would yield the `b'...'` repr).
        # 0xc1 is a never-valid UTF-8 lead byte → U+FFFD.
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        conn.execute("CREATE TABLE b (x BLOB)")
        conn.execute("INSERT INTO b VALUES (X'6869c1')")  # 'h', 'i', 0xc1
        result = _db_query(caller, conn, "SELECT x FROM b", [])
        assert _decode_result_ok_rows(caller, result) == [["hi�"]]

    def test_bad_db_url_surfaces_as_err_not_crash(self, monkeypatch) -> None:
        # An unopenable VERA_DB_URL (a file in a missing directory) must reach
        # the program's `Err` arm, not crash the host with an uncaught sqlite3
        # traceback at connection-open time.  Before the deferred-open fix,
        # `register_db` raised `sqlite3.OperationalError` during setup.
        monkeypatch.setenv(
            "VERA_DB_URL", "sqlite:////no_such_dir_1145_xyz/db.sqlite",
        )
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<DB>)
{
  match DB.query("SELECT 1", []) {
    Ok(@Array<Array<Option<String>>>) -> 0,
    Err(@String) -> 42
  }
}
"""
        assert _run(src) == 42


class TestDbEndToEnd229:
    """S4: a real Vera program using ``<DB>`` compiles (checker → codegen
    routing → ``register_db`` → sqlite) and runs end-to-end against the default
    in-memory database — no config needed."""

    _QUERY_ROWS = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<DB>)
{
  let @Result<Int, String> = DB.execute("CREATE TABLE t (name TEXT)", []);
  let @Result<Int, String> = DB.execute("INSERT INTO t VALUES (?)", [Some("alice")]);
  let @Result<Int, String> = DB.execute("INSERT INTO t VALUES (?)", [None]);
  match DB.query("SELECT name FROM t", []) {
    Ok(@Array<Array<Option<String>>>) -> array_length(@Array<Array<Option<String>>>.0),
    Err(@String) -> 0 - 1
  }
}
"""

    def test_query_row_count(self) -> None:
        # Two rows inserted (one with a NULL name, so the grid carries a None
        # cell) → the query round-trips to a 2-row grid.
        assert _run(self._QUERY_ROWS) == 2

    def test_query_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        # The S2 rooting holds through the REAL host path: baked into $rt.alloc,
        # every allocation in the grid marshalling fires $rt.gc_collect, yet the
        # row count reads back correct.
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(self._QUERY_ROWS) == 2

    def test_execute_rowcount(self) -> None:
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<DB>)
{
  let @Result<Int, String> = DB.execute("CREATE TABLE t (n INTEGER)", []);
  let @Result<Int, String> = DB.execute("INSERT INTO t VALUES (1)", []);
  let @Result<Int, String> = DB.execute("INSERT INTO t VALUES (2)", []);
  match DB.execute("DELETE FROM t", []) {
    Ok(@Int) -> @Int.0,
    Err(@String) -> 0 - 1
  }
}
"""
        assert _run(src) == 2  # DELETE removed both rows

    def test_param_injection_is_bound_as_literal(self) -> None:
        # The runtime half of the #309 guarantee: an injection-looking param is
        # bound as a value (matches nothing), and the table survives — the query
        # after still sees the one real row.
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<DB>)
{
  let @Result<Int, String> = DB.execute("CREATE TABLE u (name TEXT)", []);
  let @Result<Int, String> = DB.execute("INSERT INTO u VALUES (?)", [Some("bob")]);
  match DB.query("SELECT name FROM u WHERE name = ?", [Some("bob'; DROP TABLE u--")]) {
    Ok(@Array<Array<Option<String>>>) -> match DB.query("SELECT name FROM u", []) {
      Ok(@Array<Array<Option<String>>>) -> array_length(@Array<Array<Option<String>>>.0),
      Err(@String) -> 0 - 2
    },
    Err(@String) -> 0 - 1
  }
}
"""
        assert _run(src) == 1  # table intact — still one row


class TestDbOnDiskExample229:
    """``examples/sqlitedb.vera`` reads the committed on-disk
    ``examples/sqlitedb.sqlite`` fixture.  ``scripts/check_examples`` only
    type-checks + verifies examples (it never runs them), and this one is
    written to exit 0 either way — the on-disk read *and* the graceful
    in-memory ``Err`` arm — so without this test the on-disk read path, the
    whole point of the example, would never execute in CI.  Running the actual
    example file against the committed fixture pins the rendered city table
    (including the nullable-country ``NULL`` rendering) and doubles as a smoke
    test that the committed ``.sqlite`` is intact."""

    def test_reads_committed_fixture_and_prints_city_table(self) -> None:
        sqlite_path = _EXAMPLES / "sqlitedb.sqlite"
        assert sqlite_path.is_file(), sqlite_path
        # POSIX form + ``sqlite:///`` prefix so the URL is portable on Windows
        # (backslashes would break the path); ``_open_connection`` strips the
        # prefix back to the absolute filesystem path.  Thread the URL through
        # ``execute(env_vars=...)`` rather than mutating ``os.environ`` — the
        # explicit-dict form the ``_open_connection`` unit tests use.
        source = (_EXAMPLES / "sqlitedb.vera").read_text(encoding="utf-8")
        result = execute(
            _compile_ok(source),
            env_vars={"VERA_DB_URL": f"sqlite:///{sqlite_path.as_posix()}"},
        )
        # ``main`` returns the row count on the Ok arm — four cities in the fixture.
        assert result.value == 4
        out = result.stdout
        assert "read 4 cities from the on-disk database:" in out
        # Every city renders; the nullable country column shows NULL for
        # 'Atlantis' (a None cell) — distinct from an empty string.
        assert "Atlantis | NULL" in out
        assert "London | UK" in out
        assert "Paris | France" in out
        assert "Tokyo | Japan" in out
