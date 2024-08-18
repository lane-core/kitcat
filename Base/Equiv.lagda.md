Lane Biocini
May 04, 2024

Originally I used TypeTopology's definition from Joyal, but I settled on 1lab's
because in TypeTopology you need FunExt to show it is a proposition, whereas you
get that for free taking the contractible fibers, which makes more sense in
basic intensional MLTT. It also fits with the attitude this library wishes to
take for certain problems.

```agda

{-# OPTIONS --safe #-}

module Base.Equiv where

infix 21 _≃_

open import Prim.Prelude
open import Base.Path.Prop
open import Base.Path.Fiber

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 record is-equiv (f : A → B) : 𝓊 ⊔ 𝓋 type
   where
   no-eta-equality
   field
    is-eqv : (y : B) → is-contr (Fiber f y)

open is-equiv public

module equiv where
 module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
  idn : is-equiv {𝓊} {𝓊} {A} id
  idn .is-eqv y .ctr .pt = y
  idn .is-eqv y .ctr .path = refl
  idn .is-eqv y .paths (fib pt refl) = refl

 open is-equiv using () public

open equiv public

record Equiv {𝓊 𝓋} (A : 𝓊 type) (B : 𝓋 type): 𝓊 ⊔ 𝓋 type where
 no-eta-equality
 field
  map : A → B
  map-is-eqv : is-equiv map

open Equiv public

_≃_ : ∀ {𝓊 𝓋} → 𝓊 type → 𝓋 type → 𝓊 ⊔ 𝓋 type
A ≃ B = Equiv A B
