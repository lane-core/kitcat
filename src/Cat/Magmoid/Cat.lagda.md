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

module Cat.Magmoid.Rx (M : Magmoids) (u : ∀ x → M.unital M x) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

open import Cat.Magmoid.Base M
private module unit {x} = M.unital M (u x)
open unit renaming (unit to idn) public

module _  {x y} where
  sect : hom x y → Type h
  sect f = Σ s ∶ hom _ _ , f ⨾ s ≡ idn

  retr : hom x y → Type h
  retr f = Σ r ∶ hom _ _ , r ⨾ f ≡ idn

  is-biinv : hom x y → Type h
  is-biinv f = sect f × retr f

  is-eqv→is-biinv : {f : hom x y} → is-eqv f → is-biinv f
  is-eqv→is-biinv {f = f} p =
    (Equiv.inv ((f ⨾_) , p .snd) idn , Equiv.counit ((f ⨾_) , p .snd) idn) ,
    (Equiv.inv ((_⨾ f) , p .fst) idn , Equiv.counit ((_⨾ f) , p .fst) idn)

  id-sq : (f : hom x y) → commutative-sq f idn idn f
  id-sq f = unitl f ∙ sym (unitr f)
