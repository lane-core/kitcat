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
import Cat.Magmoid.Base as M

module Cat.Magmoid.Coh (M : Magmoids) (assoc : M.associativity M) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

open M M

has-pentagon : Type (o ⊔ h)
has-pentagon
  = ∀ {w x y z a} (f : hom w x) (g : hom x y) (k : hom y z) (l : hom z a)
  → pentagon f g k l (assoc g k l) (assoc f (g ⨾ k) l) (assoc f g k)
             (assoc f g (k ⨾ l)) (assoc (f ⨾ g) k l)

module 2-cat (units : ∀ x → unital x) where
  has-triangle : Type (o ⊔ h)
  has-triangle
    = ∀ {x y z} (f : hom x y) (g : hom y z) → triangle f g (units y) (assoc f (units y .fst) g)

  record is-2-coherent : Type (o ⊔ h) where
    no-eta-equality
    field
      tri : has-triangle
      pen : has-pentagon
