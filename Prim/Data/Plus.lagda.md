Lane Biocini
March 27st, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Data.Plus where

infixr 3 _⊎_

open import Prim.Universe

data _⊎_ {𝓊 𝓋} (X : 𝓊 type) (Y : 𝓋 type) : 𝓊 ⊔ 𝓋 type where
 inl : X → X ⊎ Y
 inr : Y → X ⊎ Y

Plus : ∀ {𝓊 𝓋} → 𝓊 type → 𝓋 type → 𝓊 ⊔ 𝓋 type
Plus = _⊎_

cases : ∀ {𝓊 𝓋 𝓌} {X : 𝓊 type} {Y : 𝓋 type} {A : X ⊎ Y → 𝓌 type}
      → ((x : X) → A (inl x))
      → ((y : Y) → A (inr y))
      → ((z : X ⊎ Y) → A z)
cases f g (inl x) = f x
cases f g (inr y) = g y

ind : ∀ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {X : 𝓌 type}
       → (A → X) → (B → X) → A ⊎ B → X
ind = cases

functor : ∀ {𝓊 𝓋 𝓌 𝓏} {A : 𝓊 type} {B : 𝓋 type} {X : 𝓌 type} {Y : 𝓏 type}
             → (f : A → X) (g : B → Y) → A ⊎ B → X ⊎ Y
functor f g = ind (λ - → inl (f -)) (λ - → inr (g -))

comm : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} → A ⊎ B → B ⊎ A
comm (inl x) = inr x
comm (inr x) = inl x
