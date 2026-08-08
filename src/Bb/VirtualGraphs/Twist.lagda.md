The twist at the primitive ternary layer. A carrier posits two
half-twist families, one of each sign. Two of the three slots of a
single reflection hold one half-twist each, so their junction — the
twist — acts on the third slot without being named as an edge of its
own. `Framing` already holds the two actions: `cell⁺` prepends the
junction to an edge and `cell⁻` appends it. Naturality and neutrality
are both statements about that occupancy, so neither one needs a cut,
a readback, or an embedding condition to be stated.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Twist where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Equiv.Base using (_≃_; is-equiv; module Equiv)
open import Core.Equiv.Properties using (is-equiv-is-prop)
open import Core.HLevel.Base using (is-prop-×; Πi-is-prop)
open import Core.Transport.J using (subst)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing
```

## The two actions

Each cell carries one half-twist of each sign, so each is the twist
itself acting on a single edge. The left action holds the edge in the
coterm flank and the right action in the term flank, and both land
back in the edge's own hom type.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where

  θ-left θ-right : ∀ {x y} → hom x y → hom x y
  θ-left  {x} {y} f = framing.cell⁺ G rx corx y (x , f)
  θ-right {x} {y} f = framing.cell⁻ G rx corx x (y , f)
```

## Naturality

The predicate reads `rx ⨾ corx ⨾ f ≡ f ⨾ rx ⨾ corx`. The twist is
central. Each side is one nested reflection, and the two sides differ
only in which flank holds the edge.

```agda
  θ-nat : Type (o ⊔ h)
  θ-nat = ∀ {x y} (f : hom x y) → θ-left f ≡ θ-right f

  θ-nat' : Type (o ⊔ h)
  θ-nat' = ∀ {x y} (f : hom x y) → θ-right f ≡ θ-left f

  θ-nat→θ-nat' : θ-nat → θ-nat'
  θ-nat→θ-nat' n f = sym (n f)

  θ-nat'→θ-nat : θ-nat' → θ-nat
  θ-nat'→θ-nat n f = sym (n f)
```

## Neutrality

Neutrality asks each action to be an equivalence. It is a property
and not a structure: being an equivalence is a proposition, and the
two universal closures and the pair inherit that.

```agda
  θ-neutral : Type (o ⊔ h)
  θ-neutral = (∀ {x y} → is-equiv (θ-left {x} {y}))
            × (∀ {x y} → is-equiv (θ-right {x} {y}))

  θ-neutral-is-prop : is-prop θ-neutral
  θ-neutral-is-prop = is-prop-×
    (Πi-is-prop λ x → Πi-is-prop λ y → is-equiv-is-prop (θ-left {x} {y}))
    (Πi-is-prop λ x → Πi-is-prop λ y → is-equiv-is-prop (θ-right {x} {y}))
```

## Halving under naturality

Naturality says the two actions agree at every edge, so under it they
are one map and each component of neutrality carries the other.

```agda
  θ-halves : θ-nat → ∀ {x y} → θ-left {x} {y} ≡ θ-right {x} {y}
  θ-halves n {x} {y} = funext (λ f → n {x} {y} f)

  θ-nat→neutral-right
    : θ-nat → ∀ {x y}
    → is-equiv (θ-left {x} {y}) → is-equiv (θ-right {x} {y})
  θ-nat→neutral-right n {x} {y} = subst is-equiv (θ-halves n {x} {y})

  θ-nat→neutral-left
    : θ-nat → ∀ {x y}
    → is-equiv (θ-right {x} {y}) → is-equiv (θ-left {x} {y})
  θ-nat→neutral-left n {x} {y} = subst is-equiv (sym (θ-halves n {x} {y}))
```

One component therefore gives the pair.

```agda
  θ-nat→neutral
    : θ-nat → (∀ {x y} → is-equiv (θ-left {x} {y})) → θ-neutral
  θ-nat→neutral n l =
    (λ {x} {y} → l {x} {y})
    , (λ {x} {y} → θ-nat→neutral-right n {x} {y} (l {x} {y}))
```

## The two inverse half-twists, extracted

Each action is an equivalence, so each family has a preimage under
it. An action carries one half-twist of each sign, so the preimage of
one family cancels that family and leaves the inverse of the other.
The two hands cross: the left action's preimage of the negative
family is the positive family's inverse, and the right action's
preimage of the positive family is the negative family's inverse.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) (N : θ-neutral G rx corx) where

  θ-left≃ θ-right≃ : ∀ {x y} → hom x y ≃ hom x y
  θ-left≃  {x} {y} = θ-left  G rx corx {x} {y} , N .fst {x} {y}
  θ-right≃ {x} {y} = θ-right G rx corx {x} {y} , N .snd {x} {y}

  corx-inv rx-inv : (x : ob) → hom x x
  corx-inv x = Equiv.inv (θ-left≃  {x} {x}) (rx   x)
  rx-inv   x = Equiv.inv (θ-right≃ {x} {x}) (corx x)

  corx-inv-counit : (x : ob) → θ-left G rx corx (corx-inv x) ≡ rx x
  corx-inv-counit x = Equiv.counit (θ-left≃ {x} {x}) (rx x)

  rx-inv-counit : (x : ob) → θ-right G rx corx (rx-inv x) ≡ corx x
  rx-inv-counit x = Equiv.counit (θ-right≃ {x} {x}) (corx x)
```
