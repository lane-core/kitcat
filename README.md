# Kitcat

An experiment with univalent programming and open source mathematics in cubical
Agda.

> **WIP** — Kitcat is currently undergoing a total rewrite in line with its new
> LLM policy. The current master is an example of what will be replaced, while
> work continues in a separate branch that will be based on agda-prelude (with
> some inspiration from 1lab's metaprogramming facilities), with univalent
> mathematics presentation written to be faithful to the Rijke textbook.
>
> While the development of the cubical infrastructure will be custom to this
> library (the development of this machinery will be much different than in
> cubical or 1lab), notation is to be influenced by Bentzen's _Naive Cubical Type Theory_
> while the mathematics arises from my own perspective and research into the
> the construction of cubical path infrastructure.

## Contents

Kitcat is a research library at the intersection of higher category theory,
homotopy type theory, and programming language foundations, written in Cubical
Agda. It is a testbed for new ideas in these areas, a reference for formalized
mathematics and type theory with machine-checked proof as its standard of
evidence. In many aspects it is my personal playground and blackboard for
exploring the design space of univalent type theory and higher category theory,
and I hope it will be useful to downstream researchers and practitioners in
these areas as well.

## Foundations

The category theory framework is built on a confluence of ideas from:

- [Capriotti-Kraus](https://arxiv.org/abs/1707.03693)
- [Chen](https://arxiv.org/abs/2503.05790)
- [Petrakis](https://arxiv.org/abs/2205.06651) and
- Sterling's [virtual bicategory theory](https://www.jonmsterling.com/005B) &
  ([reflexive graph lenses](https://arxiv.org/abs/2303.10986))
- among other references (see: resources directory)

## Acknowledgments

The primary HoTT reference used throughout is Rijke's _Introduction to Homotopy
Type Theory_, which we take as our standard reference for identifiers and
structural organization of the theory whenever possible.

While many lemmas are original (I've rewritten the Core library several times
in the course of development), Kitcat has adapted or otherwise drawn upon code
from the following projects, which are exemplars of open source mathematics and
deserve ample credit for their contributions to the foudnational corpus of
formalized Homotopy Type Theory and Univalent Foundations. They are excellent,
go look at them.

- [**1lab**](https://1lab.dev/) (Amélia Liao et al., AGPL-3.0) — Definitions
  and proofs across `Core.Function.Embedding`, `Core.HLevel`, `Core.Trait.Trunc`,
  `Core.Data.Fin`, `Core.Path`, and `Core.Transport.Properties` are derived from
  or influenced by 1lab's formalizations
- [**TypeTopology**](https://github.com/martinescardo/TypeTopology) (Martín
  Escardó et al., GPL-3.0) — `Core.Function.Partial` adapts the lifting monad
  from `Lifting.Construction`/`Lifting.Monad`; `Core.Retract` follows
  `UF.Retracts`; `Core.Discrete` follows `UF.DiscreteAndSeparated`; and
  `Core.Function.Embedding` adapts `UF.LeftCancellable`

## Related work not otherwise mentioned

- [agda-unimath](https://unimath.github.io/agda-unimath/) —
  Univalent foundations at scale, a lovely reference, and one with considerable involvement from the author of the aforementioned _Intro to HoTT_ textbook.
- [agda-categories](https://github.com/agda/agda-categories) —
  Category theory library for Agda

## LLM policy (updated 2026-07-22)

See [llm-policy](docs/llms.md) for my statement on the use of generative LLMs in this project.
