# Artifact for "Interactive Programming with Algebraic Effect Handlers and Holes"

This repository contains the artifact accompanying the paper. It has two parts:

- **[agda-mech/](agda-mech/)** — Agda mechanization of the metatheory (definitions, lemmas, and theorems of the paper's appendix), checked with `--safe`.
- **[effhole/](effhole/)** — EffHole, a prototype implementation of the language: a Haskell backend and a VS Code extension for hole-driven interactive editing.

## Requirements

| Component | Toolchain |
|---|---|
| agda-mech | Agda 2.8.0, Agda standard library 2.3 |
| effhole backend | [Stack](https://docs.haskellstack.org/) |
| effhole extension | Node.js + npm, VS Code |

## Quick start

### 1. Agda mechanization

```bash
cd agda-mech
agda Main.agda
```

Type-checks all files with no errors and no postulates beyond the extensionality module parameter (see [agda-mech/README.md](agda-mech/README.md) for details).

### 2. EffHole implementation

```bash
cd effhole/backend
stack run -- http --port 8081
```

Then in another terminal:

```bash
cd effhole/extension
npm install && npm run compile
```

Open the extension project in VS Code and press F5 to launch an Extension Development Host, then open any `.effhole` file from [effhole/examples/](effhole/examples/) and run the "Run effhole" command. See [effhole/README.md](effhole/README.md) for settings (run mode, fuel, step view).
