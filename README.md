# Kitcat: A univalent programming library for Cubical Agda

Kitcat is an experimental library for [Cubical Agda](https://agda.readthedocs.io/en/latest/index.html) centered on general purpose programming, whose underpinnings lie in a theory of **virtual categorical structures** formalized in univalent foundations, which guides the overall design and implementation of the library. This is an active research project intended as a vehicle for exploring applied univalent mathematics while pinning down useful abstractions intended to be useful to Agda hackers of all stripes.

> **WIP** — The API is not yet stable. Expect breaking changes.

## Scope

Kitcat is not a formalization library in the style of agda-categories or 1lab. Its focus is on providing an opinionated foundation for programming with categorical abstractions, with an emphasis on usability.

The library aims to provide ergonomic interfaces for both programming and formalization: functors, natural transformations, limits, adjunctions, monads — built on a modular virtual category theory framework intended to serve as a cohesive API throughout. Quality of life features and metaprogramming facilities are planned where they make sense.

Research branches may appear in alternative tags. Thin-cloning recommended.

## Foundations

The library explores a presentation of univalent type theory and higher category theory formalization drawing on Capriotti–Kraus's prior work formalizing [Univalent higher categories](https://arxiv.org/abs/1707.03693) and [∞-categorical models of HoTT](https://arxiv.org/abs/2009.01883), [Petrakis's univalent typoids](https://arxiv.org/abs/2205.06651), and Sterling's [virtual bicategory theory](https://www.jonmsterling.com/005B) and [reflexive graph lenses](https://arxiv.org/abs/2303.10986).

The core abstraction is the _virtual graph_: a graph with 2-cells satisfying a propositional contractibility condition on composites, which generalizes but is trivially satisfied by the native ∞-groupoid structure of types. Research is ongoing, but early results seem promising that this provides a suitable setting for synthetic higher category theory.

## Related Work

- [1lab](https://1lab.dev/) — Formalised mathematics as explorable reference
- [agda-unimath](https://unimath.github.io/agda-unimath/) — Systematic univalent foundations at scale
- [agda-categories](https://github.com/agda/agda-categories) — Mature category theory for the Agda ecosystem
