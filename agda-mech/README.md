# Agda Mechanization

This folder contains the Agda mechanization of the paper "Interactive Programming with Algebraic Effect Handlers and Holes", covering the definitions, lemmas, and theorems of Appendix B.

## How to run

1. Install Agda 2.8.0 and the Agda standard library 2.3.
2. Run `agda Main.agda` to check the code.

## Axiom

The only axiom used is extensionality of functions (from the standard library), passed as a module parameter. Everything is checked with `{-# OPTIONS --safe #-}`.

## Files

- [Syntax.agda](Syntax.agda): syntax of values, computations, and substitutions (hole contexts) (De Bruijn indices).
- [Subst.agda](Subst.agda): substitution and renaming operations and their standard properties.
- [Semantics.agda](Semantics.agda): small-step operational semantics.
- [Scope.agda](Scope.agda): well-scopedness judgments and hole contexts.
- [Confluence.agda](Confluence.agda): parallel reduction and confluence.
- [Filling.agda](Filling.agda): hole filling, commutativity, and fill-and-resume safety (inner modules `Pure` and `Impure` give the two symmetric cases).

## Index of names

### A.1 Small-Step Reduction Rules

Computation reduction `_-→_` is defined in [Semantics.agda:60-143](Semantics.agda#L60-L143). 

Value reduction `_-→v_` ([Semantics.agda:28-51](Semantics.agda#L28-L51)).

Substitution reduction `_-→s_` ([Semantics.agda:53-58](Semantics.agda#L53-L58)).

Multi-step reduction: `_-→*_` ([Semantics.agda:155](Semantics.agda#L155)), `_-→v*_` ([Semantics.agda:201](Semantics.agda#L201)), `_-→s*_` ([Semantics.agda:205](Semantics.agda#L205)).

### A.2 Commutativity

- **Lemma (Filling preserves well-scopedness)**: `filling-value` / `filling-comp` / `filling-subst` — [Filling.agda:152-170](Filling.agda#L152-L170) (Pure), [Filling.agda:555-573](Filling.agda#L555-L573) (Impure).
- **Lemma (Substitution commutes with filling)**: `subst-comm-c-gen` / `subst-comm-v-gen` / `subst-comm-s-gen` — [Filling.agda:239-276](Filling.agda#L239-L276) (Pure), [Filling.agda:667-695](Filling.agda#L667-L695) (Impure); single-variable instance `subst-comm-n-c` / `subst-comm-n-v` — [Filling.agda:344-364](Filling.agda#L344-L364) (Pure), [Filling.agda:741-761](Filling.agda#L741-L761) (Impure).
- **Lemma (Substitution preserves multi-step reduction)**: `substV-preserves-→v*` / `substC-preserves-→*` — [Semantics.agda:591-627](Semantics.agda#L591-L627).
- **Lemma (Weak commutativity)**: `-→--→*-comm-gen` — [Filling.agda:466-497](Filling.agda#L466-L497) (Pure), [Filling.agda:850-875](Filling.agda#L850-L875) (Impure); auxiliary case for R-β-Handle-Op: `β-op-eq-case` — [Filling.agda:382-427](Filling.agda#L382-L427) (Pure), [Filling.agda:779-824](Filling.agda#L779-L824) (Impure).
- **Theorem (Commutativity)**: `-→*-comm` — [Filling.agda:498-506](Filling.agda#L498-L506) (Pure), [Filling.agda:896-904](Filling.agda#L896-L904) (Impure).

### A.3 Confluence

- **Parallel reduction** `_⇛_` / `_⇛v_` / `_⇛s_`: [Confluence.agda:24-123](Confluence.agda#L24-L123); its closure `_⇛*_`: [Confluence.agda:159-168](Confluence.agda#L159-L168). Every one-step is parallel: `-→-to-⇛` etc. — [Confluence.agda:205-237](Confluence.agda#L205-L237); every parallel step simulates multi-step: `⇛-to-→*` etc. — [Confluence.agda:268-322](Confluence.agda#L268-L322).
- **Complete development** `ℳ`: `⇛-complete` / `⇛v-complete` — [Confluence.agda:644-673](Confluence.agda#L644-L673).
- **Lemma (Triangle property)**: `triangle-⇛` / `triangle-⇛v` — [Confluence.agda:677-782](Confluence.agda#L677-L782); diamond for `⇛*`: `confluence⇛*` — [Confluence.agda:784-793](Confluence.agda#L784-L793).
- **Theorem (Confluence)**: `confluence` — [Confluence.agda:795-801](Confluence.agda#L795-L801).

### A.4 Safety of Fill-and-Resume

- **Theorem (Fill-and-resume safety)**: `resumption` — [Filling.agda:508-513](Filling.agda#L508-L513) (Pure), [Filling.agda:906-911](Filling.agda#L906-L911) (Impure).
