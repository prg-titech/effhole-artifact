# backend

Haskell Stack project for the EffHole language core and HTTP backend.

## Dev Commands

```bash
# Build
stack build

# Test
stack test

# Start HTTP service (default port used by extension)
stack run -- http --port 8081

# Start HTTP service with custom path prefix (for proxy setups)
stack run -- http --port 8081 --base-path /effhole

# Start the interactive REPL
stack run -- repl

# stdin/stdout mode (for debugging)
echo '{"command":"eval","content":"...","fuel":1000}' | stack run -- server
```

## Structure and Module Roles

| Path | Role |
| --- | --- |
| [app/Main.hs](app/Main.hs) | Entry point, calls `CLI.cli` |
| [src/CLI.hs](src/CLI.hs) | Subcommand dispatch: repl/run/lsp/server/http |
| [src/Server.hs](src/Server.hs) | External protocol and HTTP routes; request parsing, status codes, JSON encode/decode |
| [src/Parser.hs](src/Parser.hs) | Source parsing |
| [src/Elaboration.hs](src/Elaboration.hs) | External AST to Internal AST |
| [src/Internal/](src/Internal) | `Syntax`: internal syntax, `Eval`: evaluation, `Norm`: normalization, `Pretty`: readable output and focused ranges |
| [src/External.hs](src/External.hs), [src/Type.hs](src/Type.hs), [src/Common.hs](src/Common.hs) | External syntax, type structures, shared definitions |

Core data flow:

1. parseProgram
2. elaborate
3. eval or norm (optional steps)
4. Convert result to JSON and return to frontend

## HTTP Protocol (Used by extension)

### Routes

- `GET /health`: health check, returns `{"ok": true}`.
- `POST /api/v1/run`: main execution endpoint.

### Request Body

```json
{
	"command": "eval | norm | evalStep | normStep | getHoleID",
	"content": "program text",
	"fuel": 1000
}
```

Notes:

- `getHoleID` does not require `fuel`.
- All other commands require `fuel`.

### Response Contract

- Every response includes status
- status = 0 means success
- Common error codes:
  - -1: request JSON decode failed
  - 1: parse failed
  - 2: evaluation failed
  - 3: fuel exhausted
  - 4: missing fuel
  - 5: fuel exceeds maximum allowed value
  - -2: unknown command

Successful responses may include:

- result: pretty output
- holeIds: hole counters
- substMap: context map for holes
- steps, stepCount: step execution data (evalStep/normStep)

## REPL

```bash
stack run -- repl
```

An interactive read-eval-print loop for EffHole. Example session:

```
EffHole REPL — type an expression to evaluate, :quit to exit.
> 1 + 2
3
> "hello" ^ " world"
"hello world"
> if 1 == 1 then 42 else 0
42
```

Notes:

- Empty lines are ignored; parse or evaluation errors are reported without exiting the loop.
- Type `:quit` (or `:q`), or press Ctrl-D, to exit.
- The REPL is just a prototype to show the architecture of the backend, full language features are supported via the HTTP protocol used by the extension.

## Maintenance Notes

- extension depends on command strings and field names; update [extension/src/extension.ts](../extension/src/extension.ts) when protocol changes.
- `focusedRange` and `focus` are used for frontend highlighting; validate integration when changing pretty/step structures.
