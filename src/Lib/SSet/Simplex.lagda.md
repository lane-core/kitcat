The simplex category, packaging the monotone map infrastructure
from `Core.Data.Fin.Monotone` as a `Cat` in the sense of
`Cat.Base`.

Objects are natural numbers (representing the finite ordinals
[0], [1], [2], ...) and morphisms are bundled monotone maps
between finite types. This parallels how `Lib.CSet.Cube`
packages the cube category.

Built on `Core.Data.Fin.Monotone` infrastructure.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.SSet.Simplex where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base hiding (weaken)
open import Core.Data.Fin.Monotone
open import Core.Kan using (_∙_)
open import Core.Equiv
open import Cat.Base hiding (_⇒_)

open Nat

private variable
  m n k : Nat

```

## The simplex category

The simplex category has natural numbers as objects and monotone
maps `m => n` as morphisms. Composition is diagrammatic: `f then g`
is `comp-mono g f`.

The identity at `n` is `id-mono`. The key obligation is showing that
`id-mono` is unital, meaning composition with `id-mono` is an
equivalence on both sides. Since `comp-mono g id-mono` and
`comp-mono id-mono g` are both propositionally (though not
definitionally) equal to `g`, we build the equivalences via
`iso->equiv`.

```agda

private
  -- Composition with id-mono on the right is an equivalence
  comp-idr-is-equiv
    : ∀ {m n} → is-equiv (λ (g : n ⇒ m) → comp-mono g id-mono)
  comp-idr-is-equiv =
    (iso→equiv
      (λ g → comp-mono g id-mono) id
      (λ g → comp-mono-idr g) (λ g → comp-mono-idr g))
    .snd

  -- Composition with id-mono on the left is an equivalence
  comp-idl-is-equiv
    : ∀ {m n} → is-equiv (λ (g : m ⇒ n) → comp-mono id-mono g)
  comp-idl-is-equiv =
    (iso→equiv
      (λ g → comp-mono id-mono g) id
      (λ g → comp-mono-idl g) (λ g → comp-mono-idl g))
    .snd

Delta : precategory 0ℓ 0ℓ
Delta .precategory.ob = Nat
Delta .precategory.hom m n = m ⇒ n
Delta .precategory._⨾_ f g = comp-mono g f
Delta .precategory.unital n .fst = id-mono
Delta .precategory.unital n .snd .fst = comp-idr-is-equiv , comp-idl-is-equiv
Delta .precategory.unital n .snd .snd = sym (comp-mono-idl id-mono)
Delta .precategory.assoc f g h = comp-mono-assoc h g f

```

## Face and degeneracy maps

The face map `face i : S n => n` is the monotone surjection that
duplicates at position `i`. The degeneracy map `degen i : n => S n`
is the strictly monotone injection that skips position `i`. These
are re-exported from `Core.Data.Fin.Monotone`.

```agda

face : Fin n → S n ⇒ n
face = δ

degen : Fin (S n) → n ⇒ S n
degen = σ

```

## Simplicial identities

The six families of simplicial identities, proven in
`Core.Data.Fin.Monotone`, characterize the simplex category.
They fall into three groups: cancellation (face-degeneracy),
face-face commutativity, degeneracy-degeneracy commutativity,
and face-degeneracy interchange.

All proofs use diagrammatic composition order (left-to-right).

```agda

-- Cancellation: degen then face gives identity
-- sigma (weaken i) ; delta i = id
cancel-weaken = δσ-cancel-weaken

-- sigma (fsuc i) ; delta i = id
cancel-fsuc = δσ-cancel-fsuc

-- Face-face commutativity: i <= j implies
-- delta (fsuc j) ; delta i = delta (weaken i) ; delta j
face-face = δδ-comm

-- Degeneracy-degeneracy commutativity: i <= j implies
-- sigma i ; sigma (fsuc j) = sigma j ; sigma (weaken i)
degen-degen = σσ-comm

-- Face-degeneracy interchange when i < j
-- sigma (fsuc j) ; delta (weaken i) = delta i ; sigma j
interchange-lt = δσ-interchange-lt

-- Face-degeneracy interchange when j < i
-- sigma (weaken j) ; delta (fsuc i) = delta i ; sigma j
interchange-gt = δσ-interchange-gt

```
