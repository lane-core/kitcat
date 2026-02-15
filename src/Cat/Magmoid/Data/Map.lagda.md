Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Cat.Magmoid.Type
module Cat.Magmoid.Map (M N : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

import Cat.Magmoid.Base

private
  module C = Cat.Magmoid.Base M
  module D = Cat.Magmoid.Base N

record functor : Type (C.o ⊔ D.o ⊔ C.h ⊔ D.h) where
  no-eta-equality

  field
    map  : C.ob → D.ob
    hmap : ∀ {x y}
      → C.hom x y → D.hom (map x) (map y)
    preserves-iso : ∀ {x y} (f : C.hom x y)
      → C.is-eqv f → D.is-eqv (hmap f)
    preserves-comp : ∀ {x y z}
      (f : C.hom x y) (g : C.hom y z)
      → (D._⨾_ (hmap f) (hmap g)) ≡ (hmap (C._⨾_ f g))

{-# INLINE functor.constructor #-}

```
record has-magmoid {u} o h (X : Type u) : Type (o ₊ ⊔ h ₊ ⊔ u) where
  no-eta-equality
  field
    ob : X → Type o
    hom : ∀ x → ob x → ob x → Type h
    cut : ∀ x {a b c} → hom x a b → hom x b c → hom x a c

  mag : (X : X) → Mag
  mag X .Mag.o = _
  mag X .Mag.h = _
  mag X .Mag.ob = ob X
  mag X .Mag.hom = hom X
  mag X .Mag._⨾_ = cut X

magmoid-str : ∀ u o h → Type₊ (u ⊔ o ⊔ h)
magmoid-str u o h = Σ X ∶ Type u , has-magmoid o h X

module magmoid {adj : Level → Level → Level}
  (X : ∀ o h → magmoid-str (adj o h) o h)
  where
  private
    module S o h = has-magmoid (X o h .snd)
    module O {o h} X = overlay (S.mag o h X)
    module P {o h} X = pul (S.mag o h X)
    module F {o o' h h'} X Y = fun (S.mag o h X) (S.mag o' h' Y)
    module N {o o' h h'} X Y = nat (S.mag o h X) (S.mag o' h' Y)
    module H {o o' h h'} X Y = het (S.mag o h X) (S.mag o' h' Y)

  module base {o h} (A : X o h .fst) where
    open O A public
    open P A public

  module relations {o o' h h'} (A : X o h .fst) (B : X o' h' .fst) where
    open F A B public
    open N A B public
    open H A B public
