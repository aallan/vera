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
        """Serialize Python HtmlNode dict to HTML string.

        #1502: iterative — a tree built in Vera can nest past Python's
        recursion limit, and ``html_to_string`` has a total signature.
        The stack holds nodes still to render and the closing tags (plain
        ``str``) an element queued behind its children.
        """
        parts: list[str] = []
        stack: list[dict[str, Any] | str] = [node]
        while stack:
            current = stack.pop()
            if isinstance(current, str):
                parts.append(current)
                continue
            tag = current.get("tag", "text")
            if tag == "text":
                parts.append(_html_escape(str(current.get("content", ""))))
                continue
            if tag == "comment":
                content = str(current.get("content", "")).replace(
                    "-->", "-- >",
                )
                parts.append(f"<!--{content}-->")
                continue
            # element
            name = current.get("name", "div")
            attrs: dict[str, str] = current.get("attrs", {})
            children: list[Any] = current.get("children", [])
            attr_str = ""
            for k, v in attrs.items():
                attr_str += f' {k}="{_html_escape_attr(v)}"'
            if str(name).lower() in (
                "area", "base", "br", "col", "embed", "hr", "img",
                "input", "link", "meta", "param", "source", "track",
                "wbr",
            ):
                parts.append(f"<{name}{attr_str}>")
                continue
            parts.append(f"<{name}{attr_str}>")
            stack.append(f"</{name}>")
            stack.extend(reversed(children))
        return "".join(parts)

    def _html_query_py(
        node: dict[str, Any], selector: str,
    ) -> list[dict[str, Any]]:
        """Simple CSS selector query on HtmlNode tree.

        Descendant combinator semantics: at an element matching the
        selector part it is looking for, a walk either records the element
        (last part) or continues into the children looking for the next
        part, and then, regardless, restarts from the first part in every
        child.  #1502: the walk is iterative, an explicit stack popped in
        exactly the order the recursive walk visited, so the matches and
        their order are unchanged.
        """
        results: list[dict[str, Any]] = []
        parts = selector.strip().split()
        if not parts:
            return results
        stack: list[tuple[dict[str, Any], int]] = [(node, 0)]
        while stack:
            current, depth = stack.pop()
            if current.get("tag") != "element":
                continue
            children: list[dict[str, Any]] = current.get("children", [])
            continue_into: list[tuple[dict[str, Any], int]] = []
            if _html_matches_selector(current, parts[depth]):
                if depth == len(parts) - 1:
                    results.append(current)
                else:
                    continue_into = [(c, depth + 1) for c in children]
            # LIFO: the restarts run after every continuation.
            stack.extend((c, 0) for c in reversed(children))
            stack.extend(reversed(continue_into))
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

    def _html_text_py(node: dict[str, Any]) -> str:
        """Extract the text content of an HtmlNode, in document order.

        #1502: iterative, for the same reason as ``_html_to_string_py``.
        """
        parts: list[str] = []
        stack: list[dict[str, Any]] = [node]
        while stack:
            current = stack.pop()
            tag = current.get("tag", "text")
            if tag == "text":
                parts.append(str(current.get("content", "")))
            elif tag != "comment":
                stack.extend(reversed(current.get("children", [])))
        return "".join(parts)

    if "html_parse" in ops_used:
        def host_html_parse(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            text = _read_wasm_string(caller, ptr, length)
            # Parse-domain errors → Result.Err.  #1502: ``html_parse``
            # returns a ``Result``, so EVERY failure of the parse on
            # this text is its ``Err`` — not only the three exception
            # classes this used to list.  The parse touches no WASM
            # memory, so nothing raised here is a runtime-invariant
            # violation; those live in the marshalling below, which
            # stays outside the ``try`` and now has no input-dependent
            # failure of its own.
            try:
                parser = _VeraHTMLParser()
                parser.feed(text)
                root = parser.get_root()
            except Exception as exc:  # noqa: BLE001 — host boundary; any parse failure becomes Result.Err
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
                # be reclaimed if write_html grew the heap
                # mid-walk.  Push arr_ptr; each match is written
                # through ``guard``, and (#1502) ``write_html``
                # releases its own roots before returning, so the
                # window's use no longer grows with the matches'
                # subtrees.  The
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
