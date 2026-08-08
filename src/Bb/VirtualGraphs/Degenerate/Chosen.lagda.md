The chosen-edge carrier. One family `idn` fills both argument slots,
and nothing aligns the reflection with it. The vocabulary is the
framing read at that diagonal, taken from `Framing` rather than
stated again.

A hand is named for the slot its second factor enters, `⁻` the
coterm slot and `⁺` the term slot. The framing names a hand for the
polarity of its cut. The two registers cross, so this dialect's `⁻`
hand is the framing's `⁺` hand, and its `⁺` hand the framing's `⁻`.

The engine is contractibility of `reflect`'s fiber over its own
image, from two tiers, composability and unitality. It reads no
readback, no interchange, and no embedding condition. Each hand's
projected unit makes a reflected edge its own composite, so the
fiber is a composability fiber transported along one unit law.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Chosen where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (subst; J)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding
  using (is-embedding; is-embedding→ap-equiv; ap-is-embedding)

open import Core.Rx.Type
open import Core.Rx.Base

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (is-representable; normal)
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Graph using (rxgraph)
```

## The vocabulary, axiom-free

The vocabulary is the framing read at the diagonal, so it is taken
from there rather than built again. Only the argument constructors
are proper to this register: `argue` pairs the two halves, and
`intro` and `elim` place an edge in one half against an anonymous
endpoint.

The composition register is the one place the two dialects disagree.
Here a hand is named for the slot its second factor enters, and in
the framing for the polarity of the cut, so each sign denotes the
other one's. The two lines below are where that crossing is stated.

```agda
module chosen {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open framing G idn idn public
    using (var; covar; eval; coact-π; act-π; coact; act)

  argue : ∀ {x y} → term x → coterm y → argument x y
  argue h k = h , k

  intro : ∀ {x y} → hom x y → term y
  intro {x} f = x , f

  elim : ∀ {x y} → hom x y → coterm x
  elim {y = y} f = y , f

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ = framing⁻.composite⁺ G idn

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ = framing⁺.composite⁻ G idn
```

## Composability, and the distributive laws

Each action distributes over its own hand's composition. Stated at
the edge level the anonymous endpoint is a parameter rather than a
component, so the two forms below are the same witness read at one
argument and then bundled.

```agda
  module composable
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁻ f g)))
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁺ f g)))
    where

    _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁻ g = contr⁻ f g .center .fst

    _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾⁺ g = contr⁺ f g .center .fst

    reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → reflect (f ⨾⁻ g) ≡ composite⁻ f g
    reflect-⨾⁻ f g = contr⁻ f g .center .snd

    reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → reflect (f ⨾⁺ g) ≡ composite⁺ f g
    reflect-⨾⁺ f g = contr⁺ f g .center .snd

    coact-π-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
               → coact-π (p ⨾⁻ q) e ≡ coact-π p (coact q e)
    coact-π-⨾⁻ {x} p q e i = reflect-⨾⁻ p q i (argue (var x) e)

    act-π-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
             → act-π (p ⨾⁺ q) t ≡ act-π q (act p t)
    act-π-⨾⁺ {z = z} p q t i = reflect-⨾⁺ p q i (argue t (covar z))

    coact-⨾⁻ : ∀ {x y z} (p : hom x y) (q : hom y z) (e : coterm z)
             → coact (p ⨾⁻ q) e ≡ coact p (coact q e)
    coact-⨾⁻ p q e i = e .fst , coact-π-⨾⁻ p q e i

    act-⨾⁺ : ∀ {x y z} (p : hom x y) (q : hom y z) (t : term x)
           → act (p ⨾⁺ q) t ≡ act q (act p t)
    act-⨾⁺ p q t i = t .fst , act-π-⨾⁺ p q t i
```

## The reflexive-graph dictionary

The chosen edge is a reflexivity datum: a term at `x` is the cofan of
`x`, a coterm the fan, and the two axiom halves are the centres
reflexivity provides. `Graph` states that reading over a framing, and
this graph is its diagonal.

```agda
module dict {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn

  graph : reflexive-graph o h
  graph = rxgraph G idn
```

The coslice at `a` carries the edges out of `a`, with a displayed
edge over `p` recording that its target is a composite; displayed
reflexivity is the flank absorption. Against that display the `⁻`
hand's composability is the covariant fibration condition, its
pushforward the composition, and its lift the head-rewriting
witness. The `⁺` hand is the mirror: the slice at a fixed target is
a contravariant fibration whose pullback is the composition.

```agda
  module hand⁻
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁻ f g)))
    where

    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾ g = contr⁻ f g .center .fst

    reflect-⨾ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → reflect (f ⨾ g) ≡ composite⁻ f g
    reflect-⨾ f g = contr⁻ f g .center .snd

  module hand⁺
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁺ f g)))
    where

    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
    f ⨾ g = contr⁺ f g .center .fst

    reflect-⨾ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → reflect (f ⨾ g) ≡ composite⁺ f g
    reflect-⨾ f g = contr⁺ f g .center .snd
```

