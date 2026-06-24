"""HTML effect host bindings (§9.7.4).

Extracted verbatim from `execute()` in `vera/codegen/api.py` (#421); the host
callbacks call the module-level heap helpers in `vera.runtime.heap`.
"""

from __future__ import annotations

from typing import Any

import wasmtime

from vera.runtime.heap import (
    _alloc_map_wrapper,
    _alloc_result_err_string,
    _alloc_result_ok_i32,
    _alloc_string,
    _call_alloc,
    _decode_attrs,
    _read_i32,
    _read_wasm_string,
    _ShadowGuard,
    _write_i32,
)


def register_html(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested HTML host functions on `linker`."""
    from html.parser import HTMLParser as _HTMLParser

    from vera.wasm.html_serde import read_html, write_html

    class _VeraHTMLParser(_HTMLParser):
        """Lenient HTML parser producing a tree of node dicts."""

        def __init__(self) -> None:
            super().__init__(convert_charrefs=True)
            self._root: dict[str, Any] = {
                "tag": "element", "name": "html",
                "attrs": {}, "children": [],
            }
            self._stack: list[dict[str, Any]] = [self._root]

        def handle_starttag(
            self, tag: str, attrs: list[tuple[str, str | None]],
        ) -> None:
            node: dict[str, Any] = {
                "tag": "element",
                "name": tag,
                "attrs": {k: (v or "") for k, v in attrs},
                "children": [],
            }
            self._stack[-1]["children"].append(node)
            # Void elements don't get pushed
            if tag.lower() not in (
                "area", "base", "br", "col", "embed", "hr", "img",
                "input", "link", "meta", "param", "source", "track",
                "wbr",
            ):
                self._stack.append(node)

        def handle_endtag(self, tag: str) -> None:
            # Pop back to matching tag (lenient)
            for i in range(len(self._stack) - 1, 0, -1):
                if self._stack[i]["name"] == tag:
                    self._stack[i + 1:] = []
                    break

        def handle_data(self, data: str) -> None:
            if data:
                self._stack[-1]["children"].append(
                    {"tag": "text", "content": data},
                )

        def handle_comment(self, data: str) -> None:
            self._stack[-1]["children"].append(
                {"tag": "comment", "content": data},
            )

        def get_root(self) -> dict[str, Any]:
            children: list[Any] = self._root["children"]
            if len(children) == 1 and children[0].get("tag") == "element":
                result: dict[str, Any] = children[0]
                return result
            return self._root

    def _html_escape(s: str) -> str:
        """Escape &, <, > for HTML text content."""
        return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

    def _html_escape_attr(s: str) -> str:
        """Escape &, <, >, " for HTML attribute values."""
        return (s.replace("&", "&amp;").replace("<", "&lt;")
                 .replace(">", "&gt;").replace('"', "&quot;"))

    def _html_to_string_py(node: dict[str, Any]) -> str:
        """Serialize Python HtmlNode dict to HTML string."""
        tag = node.get("tag", "text")
        if tag == "text":
            return _html_escape(str(node.get("content", "")))
        if tag == "comment":
            content = str(node.get("content", "")).replace("-->", "-- >")
            return f"<!--{content}-->"
        # element
        name = node.get("name", "div")
        attrs: dict[str, str] = node.get("attrs", {})
        children: list[Any] = node.get("children", [])
        attr_str = ""
        for k, v in attrs.items():
            attr_str += f' {k}="{_html_escape_attr(v)}"'
        if str(name).lower() in (
            "area", "base", "br", "col", "embed", "hr", "img",
            "input", "link", "meta", "param", "source", "track",
            "wbr",
        ):
            return f"<{name}{attr_str}>"
        inner = "".join(_html_to_string_py(c) for c in children)
        return f"<{name}{attr_str}>{inner}</{name}>"

    def _html_query_py(
        node: dict[str, Any], selector: str,
    ) -> list[dict[str, Any]]:
        """Simple CSS selector query on HtmlNode tree."""
        results: list[dict[str, Any]] = []
        parts = selector.strip().split()
        if not parts:
            return results
        _html_query_walk(node, parts, 0, results)
        return results

    def _html_matches_selector(
        node: dict[str, Any], sel: str,
    ) -> bool:
        """Check if a single element matches a simple selector."""
        if node.get("tag") != "element":
            return False
        name = str(node.get("name", ""))
        attrs: dict[str, str] = node.get("attrs", {})
        if sel.startswith("#"):
            return bool(attrs.get("id", "") == sel[1:])
        if sel.startswith("."):
            classes = str(attrs.get("class", "")).split()
            return sel[1:] in classes
        if sel.startswith("[") and sel.endswith("]"):
            attr_name = sel[1:-1]
            return bool(attr_name in attrs)
        return bool(name == sel)

    def _html_query_walk(
        node: dict[str, Any],
        parts: list[str],
        depth: int,
        results: list[dict[str, Any]],
    ) -> None:
        """Walk tree matching descendant combinator selectors."""
        if node.get("tag") != "element":
            return
        if _html_matches_selector(node, parts[depth]):
            if depth == len(parts) - 1:
                results.append(node)
            else:
                # Continue matching remaining parts in descendants
                for child in node.get("children", []):
                    _html_query_walk(child, parts, depth + 1, results)
        # Always try matching from the start in all descendants
        for child in node.get("children", []):
            _html_query_walk(child, parts, 0, results)

    def _html_text_py(node: dict[str, Any]) -> str:
        """Extract text content recursively from HtmlNode."""
        tag = node.get("tag", "text")
        if tag == "text":
            return str(node.get("content", ""))
        if tag == "comment":
            return ""
        # element — concatenate children text
        children: list[Any] = node.get("children", [])
        return "".join(
            _html_text_py(c) for c in children
        )

    if "html_parse" in ops_used:
        def host_html_parse(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            text = _read_wasm_string(caller, ptr, length)
            # Parse-domain errors → Result.Err.  Narrow catch:
            # parser failures (lenient HTMLParser raising on a
            # genuinely malformed input) surface as
            # ``Result.Err(str(exc))``.  We deliberately do NOT
            # catch invariant violations (e.g. the
            # ``_wrap_handle`` RuntimeError from #578 for an
            # out-of-range handle, or any AssertionError from
            # internal compiler bugs); those propagate as
            # wasmtime traps so the diagnostic text reaches
            # the user instead of being repackaged.
            try:
                parser = _VeraHTMLParser()
                parser.feed(text)
                root = parser.get_root()
            except (ValueError, TypeError, AttributeError) as exc:
                return _alloc_result_err_string(caller, str(exc))
            # #692: hold the shadow-stack window open across
            # the full tree marshalling AND the final
            # Result.Ok wrapper alloc.  Shadow-stack work is
            # OUTSIDE the parse try/except so host-side
            # invariant violations (``_ShadowGuard`` overflow,
            # ``_wrap_handle`` RuntimeError, AssertionErrors)
            # propagate as wasmtime traps rather than being
            # repackaged as user-domain parse errors.  Matches
            # ``host_md_parse`` and ``host_json_parse``
            # structurally — caught by pr-review-toolkit:
            # before this restructure, the with-block was
            # inside the narrow except above, contradicting
            # the comment that claimed otherwise.
            with _ShadowGuard(caller) as guard:
                html_ptr = write_html(
                    caller, _call_alloc, _write_i32,
                    _alloc_string, _alloc_map_wrapper,
                    guard, root,
                )
                guard.push(html_ptr)
                return _alloc_result_ok_i32(caller, html_ptr)

        linker.define_func(
            "vera", "html_parse",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_html_parse, access_caller=True,
        )

    if "html_to_string" in ops_used:
        def host_html_to_string(
            caller: wasmtime.Caller, ptr: int,
        ) -> tuple[int, int]:
            node = read_html(
                caller, ptr, _read_i32,
                _read_wasm_string, _decode_attrs,
            )
            text = _html_to_string_py(node)
            return _alloc_string(caller, text)

        linker.define_func(
            "vera", "html_to_string",
            wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            ),
            host_html_to_string, access_caller=True,
        )

    if "html_query" in ops_used:
        def host_html_query(
            caller: wasmtime.Caller,
            node_ptr: int, sel_ptr: int, sel_len: int,
        ) -> tuple[int, int]:
            node = read_html(
                caller, node_ptr, _read_i32,
                _read_wasm_string, _decode_attrs,
            )
            selector = _read_wasm_string(caller, sel_ptr, sel_len)
            matches = _html_query_py(node, selector)
            count = len(matches)
            if count > 0:
                # #692: same shadow-stack-rooting concern as
                # ``host_html_parse`` — arr_ptr would otherwise
                # be reclaimed if a recursive write_html grew
                # the heap mid-walk.  Push arr_ptr; each child
                # write also routes through ``guard``.  The
                # returned (arr_ptr, count) pair is unrooted
                # at the point of return (``__exit__`` resets
                # ``$gc_sp`` before the function returns); the
                # WASM-side caller is responsible for re-rooting
                # via ``gc_shadow_push`` once the values land in
                # locals — emitted by ``_translate_html_query``
                # in ``vera/wasm/calls_markup.py``.  Safe in
                # practice because no allocation happens between
                # the call return and the receiving local-store,
                # but the guard's protection does NOT extend past
                # the function boundary.
                with _ShadowGuard(caller) as guard:
                    arr_ptr = _call_alloc(caller, count * 4)
                    guard.push(arr_ptr)
                    for i, m in enumerate(matches):
                        m_ptr = write_html(
                            caller, _call_alloc, _write_i32,
                            _alloc_string, _alloc_map_wrapper,
                            guard, m,
                        )
                        _write_i32(caller, arr_ptr + i * 4, m_ptr)
            else:
                arr_ptr = 0
            return (arr_ptr, count)

        linker.define_func(
            "vera", "html_query",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(),
                 wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            ),
            host_html_query, access_caller=True,
        )

    if "html_text" in ops_used:
        def host_html_text(
            caller: wasmtime.Caller, ptr: int,
        ) -> tuple[int, int]:
            node = read_html(
                caller, ptr, _read_i32,
                _read_wasm_string, _decode_attrs,
            )
            text = _html_text_py(node)
            return _alloc_string(caller, text)

        linker.define_func(
            "vera", "html_text",
            wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            ),
            host_html_text, access_caller=True,
        )
