# Kitcat Design Philosophy

Kitcat is a **practical programming library** built on univalent type theory.

## What Kitcat Is

**A practical standard library for cubical Agda.** Kitcat provides data
structures, algorithms, and abstractions familiar to Haskell/Idris2
programmers, grounded in homotopy type theory. It aims to be correct,
performant, and suitable for real programming work.

**For coders and researchers.** Kitcat serves both programmers who want
a dependable standard library and researchers exploring cubical type
theory's computational features—without repeating boilerplate.

**Ergonomic and opinionated.** APIs are modeled on the Idris2 standard
library where applicable—`Eq`, `Ord`, `Functor`, `Monad`—adapted to the
unique character of programming in univalent type theory. We reference
1lab for idiomatic cubical Agda patterns.

**Self-contained and performant.** No external dependencies. Code is
written with performance in mind; correctness and efficiency are both
goals, not trade-offs.

## Core Principles

1. **Correct and performant.** Both are goals. Code should be provably
   correct AND efficient enough for real use.

2. **Minimalism.** Every definition earns its place. No abstraction
   without immediate use.

3. **Composability.** Small, orthogonal pieces that combine powerfully.

4. **Clarity over cleverness.** Readable proofs beat terse ones—but
   don't sacrifice performance for readability theater.

5. **Cubical idioms.** Prefer direct path algebra and hcom constructions
   over transport-heavy approaches when they simplify proofs or improve
   computational behavior.

## What Kitcat Is Not

- **Not a mathematical knowledge repository.** Unlike 1lab (which we
  reference for idiomatic cubical patterns), Kitcat is a programming
  library first. We formalize what we need for practical use, not
  everything that could be formalized.

- **Not a HoTT textbook.** Code should be self-explanatory to readers
  familiar with the concepts; we don't re-explain standard theory.

## Design Decisions

### Module Organization
- `Core.*` — Stable foundational primitives
- `Data.*` — Concrete data types and properties
- `Trait.*` — Typeclass-like interfaces (Idris2-style)
- `Meta.*` — Metaprogramming and tactics

### Style
See `STYLEGUIDE.md` for formatting and naming conventions.

### Safety
All code must compile with:
```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}
```
No postulates or unsafe features without explicit authorization.

## References

- **STYLEGUIDE.md** — Formatting and naming conventions
- **Rijke's Introduction to HoTT** — Primary mathematical reference
- **1lab** (https://1lab.dev) — Idiomatic cubical Agda patterns
- **Cubical Agda library** — Reference for cubical primitives
