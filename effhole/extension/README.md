# extension

VS Code extension project for EffHole editor interaction, backend requests, and result rendering.

## Dev Commands

```bash
# Install dependencies
npm install

# Compile
npm run compile

# Watch mode
npm run watch

# lint
npm run lint

# Test
npm test
```

Open the extension folder in VS Code and press F5 to launch an Extension Development Host.

## Main Structure

| Path | Role |
| --- | --- |
| [src/extension.ts](src/extension.ts) | `activate` registers commands and inlay hints; reads settings, builds requests, calls backend; manages webview and step view |
| [media/view.html](media/view.html) | Normal result UI (output, hole context, step controls) |
| [media/error.html](media/error.html) | Error UI |
| [package.json](package.json) | Commands, keybindings, language extension, and settings declarations |

## Commands and Interaction

- effhole.run / effhole.runWithKeys
	- Execute eval or norm on current .effhole file (optional step mode)
- effhole.normalizeSelection
	- Normalize selected text and show popup result
- inlay hints
	- Fetch hole markers via getHoleID and render in editor

## Backend Protocol

The extension always calls:

- `GET {serverUrl}/health`
- `POST {serverUrl}/api/v1/run`

Request body:

```json
{
	"command": "eval | norm | evalStep | normStep | getHoleID",
	"content": "program text",
	"fuel": 1000
}
```

Notes:

- `getHoleID` does not require `fuel`.
- Other commands require `fuel` in range 1..2000.

Key response fields:

- status: 0 means success, non-zero means failure
- result: main output text
- substMap: context for holes
- steps: step list (step mode)
- focusedRange + focus: highlight position in frontend

Common error status codes:

- -1: request JSON decode failed
- 1: parse failed
- 2: evaluation failed
- 3: fuel exhausted
- 4: missing fuel
- 5: fuel exceeds maximum allowed value
- -2: unknown command

## Settings

- Run mode: toggle in the editor title bar (eval/norm button)
- effhole.step: enable step mode
- effhole.fuel: fuel (1..2000)
- effhole.serverUrl: backend URL, default http://127.0.0.1:8081
- effhole.requestTimeoutMs: request timeout

## Maintenance Notes

- Keep command/status/field names aligned with [backend/src/Server.hs](../backend/src/Server.hs).
- When `steps` or `focusedRange` changes, update highlighting and step navigation logic in [src/extension.ts](src/extension.ts).
