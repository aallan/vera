// Vera language extension: starts `vera lsp` for .vera files.
//
// The grammar and language configuration are declarative (see
// package.json `contributes`) and work with no code at all; this
// module only wires up the language server. It degrades gracefully:
// if the `vscode-languageclient` dependency is absent (a from-source
// symlink install without `npm install`) or `vera.lsp.enabled` is
// off, the extension stays a syntax-highlighting extension and
// nothing errors.

"use strict";

const fs = require("fs");
const path = require("path");
const vscode = require("vscode");

let client;
let channel;

function log(message) {
    if (!channel) {
        channel = vscode.window.createOutputChannel("Vera Language Server");
    }
    channel.appendLine(message);
}

function loadLanguageClient() {
    try {
        return require("vscode-languageclient/node");
    } catch (err) {
        log(
            "vscode-languageclient is not installed; running in " +
            "syntax-highlighting-only mode. For language-server " +
            "features (proof-aware diagnostics, hover, slot " +
            "go-to-definition, hole completion), run `npm install` " +
            "in the extension directory. " + err.message,
        );
        return null;
    }
}

function resolveServerCommand() {
    const config = vscode.workspace.getConfiguration("vera.lsp");
    const configured = config.get("path", "vera");
    if (configured !== "vera") {
        return configured; // an explicit setting always wins
    }
    // VS Code launched from the GUI does not inherit a shell PATH, so
    // a bare "vera" rarely resolves to the right binary (or at all).
    // The from-source layout keeps a venv inside the workspace —
    // prefer that before falling back to PATH.
    for (const folder of vscode.workspace.workspaceFolders ?? []) {
        for (const rel of [
            path.join(".venv", "bin", "vera"),
            path.join(".venv", "Scripts", "vera.exe"),
        ]) {
            const candidate = path.join(folder.uri.fsPath, rel);
            if (fs.existsSync(candidate)) {
                return candidate;
            }
        }
    }
    return configured;
}

function buildClient(lc) {
    const command = resolveServerCommand();
    const serverOptions = {
        command,
        args: ["lsp"],
    };
    const clientOptions = {
        documentSelector: [
            { scheme: "file", language: "vera" },
            { scheme: "untitled", language: "vera" },
        ],
        outputChannelName: "Vera Language Server",
    };
    log(`Starting language server: ${command} lsp`);
    return new lc.LanguageClient(
        "vera",
        "Vera Language Server",
        serverOptions,
        clientOptions,
    );
}

async function startClient(lc) {
    client = buildClient(lc);
    try {
        await client.start();
    } catch (err) {
        // Most common cause: no `vera` binary on PATH, or the [lsp]
        // extra is not installed. The client already surfaced its own
        // error UI; add the actionable detail to the channel.
        log(
            "Failed to start `vera lsp`. Check that the vera binary " +
            "is on PATH (or set the vera.lsp.path setting) and that " +
            'the [lsp] extra is installed: pip install -e ".[lsp]". ' +
            "Details: " + err.message,
        );
        client = undefined;
        // One actionable toast — the silent output-channel line made
        // "nothing is showing up" needlessly hard to diagnose.
        const choice = await vscode.window.showWarningMessage(
            "Vera language server failed to start (syntax highlighting " +
            "still works). Point the vera.lsp.path setting at your " +
            "vera binary, e.g. .venv/bin/vera in a clone.",
            "Open Settings",
        );
        if (choice === "Open Settings") {
            await vscode.commands.executeCommand(
                "workbench.action.openSettings", "vera.lsp.path",
            );
        }
    }
}

async function activate(context) {
    const config = vscode.workspace.getConfiguration("vera.lsp");
    if (!config.get("enabled", true)) {
        log("vera.lsp.enabled is false; language server not started.");
        return;
    }
    const lc = loadLanguageClient();

    context.subscriptions.push(
        vscode.commands.registerCommand("vera.lsp.restart", async () => {
            if (client) {
                await client.stop();
                client = undefined;
            }
            if (lc) {
                await startClient(lc);
            } else {
                log(
                    "Cannot restart: vscode-languageclient is not " +
                    "installed.",
                );
            }
        }),
    );

    if (lc) {
        await startClient(lc);
    }
}

function deactivate() {
    if (client) {
        const stopping = client.stop();
        client = undefined;
        return stopping;
    }
    return undefined;
}

module.exports = { activate, deactivate };
