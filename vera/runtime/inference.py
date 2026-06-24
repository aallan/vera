"""Inference effect host bindings.

Extracted from `execute()` in `vera/codegen/api.py` (#421).  Includes the LLM
provider registry and HTTP call helper, which are used only by this family.
"""

from __future__ import annotations

from dataclasses import dataclass

import wasmtime

from vera.runtime.heap import (
    _alloc_result_err_string,
    _alloc_result_ok_string,
    _read_wasm_string,
)
from vera.runtime.http import _HTTP_TIMEOUT


@dataclass(frozen=True)
class _ProviderConfig:
    """Configuration for a single LLM inference provider."""

    env_key: str         # environment variable holding the API key
    url: str             # chat completions endpoint URL
    default_model: str   # cheap/fast default when VERA_INFERENCE_MODEL is unset
    auth_style: str      # "anthropic" | "bearer"
    response_style: str  # "anthropic" | "openai"


#: Registry of supported inference providers.
#: Adding a new OpenAI-compatible provider is a one-row change here.
_PROVIDERS: dict[str, _ProviderConfig] = {
    "anthropic": _ProviderConfig(
        env_key="VERA_ANTHROPIC_API_KEY",
        url="https://api.anthropic.com/v1/messages",
        default_model="claude-haiku-4-5-20251001",
        auth_style="anthropic",
        response_style="anthropic",
    ),
    "openai": _ProviderConfig(
        env_key="VERA_OPENAI_API_KEY",
        url="https://api.openai.com/v1/chat/completions",
        default_model="gpt-4o-mini",
        auth_style="bearer",
        response_style="openai",
    ),
    "moonshot": _ProviderConfig(
        env_key="VERA_MOONSHOT_API_KEY",
        url="https://api.moonshot.ai/v1/chat/completions",
        default_model="kimi-k2-0905-preview",
        auth_style="bearer",
        response_style="openai",
    ),
    "mistral": _ProviderConfig(
        env_key="VERA_MISTRAL_API_KEY",
        url="https://api.mistral.ai/v1/chat/completions",
        default_model="mistral-small-latest",
        auth_style="bearer",
        response_style="openai",
    ),
}


def _call_inference_provider(
    provider: str,
    prompt: str,
    model: str,
    api_key: str,
) -> str:
    """Dispatch a completion request to the configured LLM provider.

    Looks up *provider* in ``_PROVIDERS``, builds the appropriate request,
    and returns the completion string.  Raises on network or API errors;
    the caller wraps the result in Ok/Err and writes it to WASM memory.
    """
    import json as _json
    import urllib.request as _urlreq

    cfg = _PROVIDERS.get(provider)
    if cfg is None:
        valid = ", ".join(sorted(_PROVIDERS))
        raise ValueError(
            f"Unknown inference provider '{provider}'. "
            f"Valid values: {valid}."
        )

    chosen_model = model or cfg.default_model

    if cfg.auth_style == "anthropic":
        headers = {
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        }
        body = _json.dumps({
            "model": chosen_model,
            "max_tokens": 1024,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")
    else:  # bearer
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        }
        body = _json.dumps({
            "model": chosen_model,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")

    req = _urlreq.Request(cfg.url, data=body, headers=headers, method="POST")  # noqa: S310
    with _urlreq.urlopen(req, timeout=_HTTP_TIMEOUT) as resp:  # noqa: S310
        raw = resp.read()
        # #591 — strict-mode `.decode("utf-8")` previously leaked
        # the raw `UnicodeDecodeError` message (including byte
        # offsets and Python-internals jargon) into the
        # `Result::Err` string the user sees from
        # `Inference.complete`.  An LLM-API response that isn't
        # valid UTF-8 is genuinely broken — we want to fail loudly
        # but with a Vera-native message, not Python noise.
        try:
            decoded = raw.decode("utf-8")
        except UnicodeDecodeError as ude:
            raise RuntimeError(
                f"Inference provider '{provider}' returned a "
                f"response body that is not valid UTF-8 "
                f"(invalid byte at position {ude.start}).",
            ) from None
        data = _json.loads(decoded)

    if cfg.response_style == "anthropic":
        return str(data["content"][0]["text"])
    else:  # openai
        return str(data["choices"][0]["message"]["content"])


def register_inference(
    linker: wasmtime.Linker,
    ops_used: set[str],
    env_vars: dict[str, str] | None,
) -> None:
    """Register the requested Inference host functions on `linker`."""
    if "inference_complete" in ops_used:
        def host_inference_complete(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            import os as _os

            prompt = _read_wasm_string(caller, ptr, length)
            _env = env_vars if env_vars is not None else _os.environ
            provider = _env.get("VERA_INFERENCE_PROVIDER", "").lower()

            # Auto-detect provider from whichever key is set,
            # respecting registry insertion order (anthropic first).
            if not provider:
                for _pname, _pcfg in _PROVIDERS.items():
                    if _env.get(_pcfg.env_key, ""):
                        provider = _pname
                        break

            if not provider:
                key_vars = ", ".join(
                    c.env_key for c in _PROVIDERS.values()
                )
                return _alloc_result_err_string(
                    caller,
                    f"No inference provider configured. "
                    f"Set {key_vars}.",
                )

            cfg = _PROVIDERS.get(provider)
            api_key = _env.get(cfg.env_key, "") if cfg else ""

            if cfg is not None and not api_key:
                return _alloc_result_err_string(
                    caller,
                    f"Inference provider '{provider}' selected but "
                    f"{cfg.env_key} is not set.",
                )

            try:
                model = _env.get("VERA_INFERENCE_MODEL", "")
                completion = _call_inference_provider(
                    provider, prompt, model, api_key,
                )
                return _alloc_result_ok_string(caller, completion)
            except Exception as exc:
                return _alloc_result_err_string(caller, str(exc))

        linker.define_func(
            "vera", "inference_complete",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_inference_complete, access_caller=True,
        )
