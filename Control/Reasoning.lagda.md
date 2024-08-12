Lane Biocini
Jun 30, 2024

Combinator for reasoning.

```
{-# OPTIONS --safe #-}

module Control.Reasoning where

open import Prim.Universe
open import Prim.Pi

record Reasoning {𝓊 𝓋 𝓌} {X : 𝓊 type} (A : X → 𝓋 type) (B : X → 𝓌 type) : 𝓤ω where
 field
  con : ∀ x → A x → B x → 𝓋 type
  seq : ∀ x → (a : A x) (b : B x) → con x a b

 infixr 40 _∙_
 _∙_ : ∀ {x} → (a : A x) (b : B x) → con x a b
 _∙_ {x} = seq x
 {-# INLINE _∙_ #-}

 _,_⊢_ : ∀ x → (a : A x) (b : B x) → con x a b
 _,_⊢_ = seq

open Reasoning ⦃ ... ⦄ hiding (con) public

-- _,_⊢_ : ∀ {𝓊 𝓋 𝓌} {X : 𝓊 type} {{A }} {B : A → 𝓋 type} {{R : Reasoning A B}}
--       → {!(x : A) → ()!}
-- _,_⊢_ = {!!}
