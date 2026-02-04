# Kitcat

An experiment in univalent programming and open source mathematics conducted in
Agda.

Kitcat is an experimental univalent mathematics and programming library written
in [Cubical Agda](https://agda.readthedocs.io/en/latest/index.html) intended to
be an ergonomic, modular, and scalable library to be used for formalized
mathematics, proof theory research, as well as ordinary functional programming.

> **WIP** — API is unstable. Expect breaking changes.

## Contents

The `Core` namespace provides cubical foundations (paths, transport,
equivalences, h-levels, Kan operations, univalence), standard data types, and
typeclass traits. `Cat` builds a virtual category theory framework — magmoids,
unitality, associativity, coherence, monads, and CwFs. `Data` and `HData`
supply concrete and higher inductive types. `Lib` contains extended
developments: cubical and semi-simplicial sets, Segal types, and modular group
theory.

Kitcat will be host to investigations at the intersection of higher catgegory
theory, homotopy type theory, rewriting theory, combinatorics, and proof
theory. The library is intended to be a testbed for new ideas in these areas,
as well as a reference for formalized mathematics and an ergonomic environment
for functional programming.

## Foundations

The category theory framework is built on a confluence of ideas from:

- [Capriotti-Kraus](https://arxiv.org/abs/1707.03693)
- [Chen](https://arxiv.org/abs/2503.05790)
- [Petrakis](https://arxiv.org/abs/2205.06651) and
- Sterling's [virtual bicategory theory](https://www.jonmsterling.com/005B) &
  ([reflexive graph lenses](https://arxiv.org/abs/2303.10986))
- among other references, including ideas from virtual double category theory
  and (obviously) homotopy type theory

## Related work

- [1lab](https://1lab.dev/): Formalised mathematics as explorable reference,
  whom this library is much indebted to
- [agda-unimath](https://unimath.github.io/agda-unimath/)
  Univalent foundations at scale
- [agda-categories](https://github.com/agda/agda-categories)
  Category theory library for Agda
