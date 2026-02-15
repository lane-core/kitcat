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
module Cat.Magmoid.Het (M N : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv
import Cat.Magmoid.Base

open import Cat.Magmoid.Map

private
  module C = Cat.Magmoid.Base M
  module D = Cat.Magmoid.Base N

record _⊣_ (F : functor M N) (G : functor N M) : Type (C.o ⊔ D.o ⊔ C.h ⊔ D.h) where
  no-eta-equality
  private
    module F = functor F
    module G = functor G

  field
    hom-equiv : ∀ x y → D.hom (F.map x) y ≃ C.hom x (G.map y)

  adjunct : ∀ {x y} → D.hom (F.map x) y → C.hom x (G.map y)
  adjunct {x} {y} = Equiv.fwd (hom-equiv x y)

  coadjunct : ∀ {x y} → C.hom x (G.map y) → D.hom (F.map x) y
  coadjunct {x} {y} = Equiv.inv (hom-equiv x y)

  field
    natural-dom
      : ∀ {x x' y} (f : C.hom x' x) (g : D.hom (F.map x) y)
      → (adjunct (D._⨾_ (F.hmap f) g)) ≡ (C._⨾_ f (adjunct g))
    natural-cod
      : ∀ {x y y'} (g : D.hom (F.map x) y) (k : D.hom y y')
      → (adjunct (D._⨾_ g k)) ≡ (C._⨾_ (adjunct g) (G.hmap k))

{-# INLINE _⊣_.constructor #-}

is-left-adjoint : functor M N → Type _
is-left-adjoint F = Σ G ∶ functor N M , F ⊣ G

is-right-adjoint : functor N M → Type _
is-right-adjoint G = Σ F ∶ functor M N , F ⊣ G
