# EffHole

EffHole is a language for experimenting with effect systems and hole-driven development. It contains:

- backend: Haskell implementation of the language core and HTTP service
- extension: VS Code extension for editor interaction and result rendering
- examples: sample programs (.effhole)

## Quick Start

1. Start the backend (default port 8081)

```bash
cd backend
stack run -- http --port 8081
```

2. Build the VS Code extension

```bash
cd extension
npm install
npm run compile
```

Then press F5 in VS Code (with the extension project open) to launch an Extension Development Host.

3. Open any .effhole file and run

- Run effhole from the command palette.
- Or press F5 inside a .effhole editor.

## How It Works

- The extension reads the active file and sends an HTTP request to backend.
- backend performs parsing, elaboration, and eval or norm.
- The extension renders results, hole context, and step view in a webview.

## Common Settings (VS Code)

- effhole.serverUrl: backend base URL, default http://127.0.0.1:8081
- effhole.runMode: eval or norm
- effhole.step: enable step-by-step mode
- effhole.fuel: evaluation/normalization fuel, default 1000
- effhole.requestTimeoutMs: request timeout in ms

## Subproject Docs

- [backend maintainer README](backend/README.md)
- [extension maintainer README](extension/README.md)
