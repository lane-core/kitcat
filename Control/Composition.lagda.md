Lane Fiocini
Jun 30, 2024

Combinator for reasoning.

We take the approach of considering some local equivalent of the Pi type
obeying certain properties

```
{-# OPTIONS --safe #-}

module Control.Composition where

open import Prim.Universe
open import Control.Arrow

record Composition ℓ {𝓊 𝓋} (A : 𝓊 type) (B : 𝓋 type) : 𝓊 ⊔ 𝓋 ⊔ ℓ ⁺ type where
 field
  mor : A → B → ℓ type
  seq : (f : A) (g : B) → mor f g

 infixr 40 _∘_
 _∘_ : (g : B) (f : A) → mor f g
 _∘_ g f = seq f g
 {-# INLINE _∘_ #-}

open Composition  ⦃ ... ⦄ hiding (mor; seq) public

module _ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : B → 𝓌 type} where
 instance
  composition-Π : Composition (𝓊 ⊔ 𝓌) (A → B) (∀ y → C y)
  composition-Π .Composition.mor = λ f _ → ∀ x → C (f x)
  composition-Π .Composition.seq f g = λ x → g (f x)
