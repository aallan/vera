"""Browser bundle emission for compiled Vera WASM modules.

Generates a self-contained browser bundle:
  - module.wasm   (compiled WASM binary)
  - runtime.mjs   (JavaScript runtime)
  - index.html    (HTML shell page)

Usage from CLI:
    vera compile --target browser examples/hello_world.vera -o /tmp/out/
"""

from __future__ import annotations

import importlib.resources
import shutil
from pathlib import Path


def _runtime_source_path() -> Path:
    """Return the path to runtime.mjs within the vera.browser package."""
    # importlib.resources.files() returns a Traversable; for installed
    # packages it may not be a real Path, so we fall back to the file
    # system path relative to this module.
    try:
        ref = importlib.resources.files("vera.browser").joinpath("runtime.mjs")
        # as_posix works for Traversable; but we need a real path for shutil
        if hasattr(ref, "__fspath__"):
            return Path(ref)  # type: ignore[arg-type]
    except (TypeError, FileNotFoundError):
        pass
    # Fallback: resolve relative to this file
    return Path(__file__).parent / "runtime.mjs"


_INDEX_HTML_TEMPLATE = """\
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>{title}</title>
  <style>
    body {{
      font-family: system-ui, -apple-system, sans-serif;
      max-width: 800px;
      margin: 2rem auto;
      padding: 0 1rem;
      background: #fafafa;
      color: #333;
    }}
    h1 {{
      font-size: 1.4rem;
      color: #555;
    }}
    pre {{
      background: #1e1e1e;
      color: #d4d4d4;
      padding: 1rem;
      border-radius: 6px;
      overflow-x: auto;
      white-space: pre-wrap;
      font-size: 0.9rem;
      line-height: 1.5;
    }}
    .error {{
      color: #f44;
    }}
    .meta {{
      color: #888;
      font-size: 0.85rem;
      margin-top: 0.5rem;
    }}
  </style>
</head>
<body>
  <h1>{title}</h1>
  <pre id="output">Loading...</pre>
  <p class="meta">Compiled with <a href="https://veralang.dev">Vera</a></p>
  <script type="module">
    import init, {{ call, getStdout, getState, getExitCode }} from './runtime.mjs';

    const output = document.getElementById('output');
    try {{
      await init('./module.wasm');
      call('main');

      const stdout = getStdout();
      const state = getState();
      const exitCode = getExitCode();

      let text = stdout || '';
      if (state && Object.keys(state).length > 0) {{
        text += '\\nState: ' + JSON.stringify(state);
      }}
      if (exitCode !== null && exitCode !== undefined) {{
        text += '\\nExit code: ' + exitCode;
      }}
      output.textContent = text || '(no output)';
    }} catch (e) {{
      output.textContent = 'Error: ' + e.message;
      output.classList.add('error');
    }}
  </script>
</body>
</html>
"""


def emit_browser_bundle(
    wasm_bytes: bytes,
    output_dir: Path,
    *,
    title: str = "Vera Program",
) -> list[Path]:
    """Write a browser bundle to *output_dir*.

    Returns the list of files written.
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Write the compiled WASM binary
    wasm_path = output_dir / "module.wasm"
    wasm_path.write_bytes(wasm_bytes)

    # 2. Copy runtime.mjs
    runtime_dst = output_dir / "runtime.mjs"
    runtime_src = _runtime_source_path()
    shutil.copy2(runtime_src, runtime_dst)

    # 3. Generate index.html
    html_path = output_dir / "index.html"
    html_path.write_text(
        _INDEX_HTML_TEMPLATE.format(title=title),
        encoding="utf-8",
    )

    return [wasm_path, runtime_dst, html_path]
