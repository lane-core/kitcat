Lane Biocini
Oct 13th, 2024

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Function.Type where

open import Lib.Prim
open import Lib.Data.Sigma using (Σ; Sigma)
open import Lib.Trait.Typoid.Type
open import Lib.Trait.Typoid.Base using (Typoid)

module _ {u₁ v₁ w₁ u₂ v₂ w₂} (𝓐 : Typoid u₁ v₁ w₁) (𝓑 : Typoid u₂ v₂ w₂) where
 private
  module 𝓐 = Typoid 𝓐
  module 𝓑 = Typoid 𝓑

 typd-associate : (𝓐.ob → 𝓑.ob) → u₁ ⊔ v₁ ⊔ w₁ ⊔ v₂ ⊔ w₂ type
 typd-associate f = Σ ϕ ꞉ ((x y : 𝓐.ob) → x 𝓐.≃ y → f x 𝓑.≃ f y)
                  , ((x y : 𝓐.ob) (e d : x 𝓐.≃ y) → e 𝓐.≅ d
                                                  → ϕ x y e 𝓑.≅ ϕ x y d)

 record is-typoid-function (f : 𝓐.ob → 𝓑.ob) : u₁ ⊔ v₁ ⊔ w₁ ⊔ v₂ ⊔ w₂ type
  where
  field
   has-associate : typd-associate f

  open Σ has-associate renaming (fst to ϕ; snd to ϕ²)
  field
   associate-id : ∀ x → ϕ x x (𝓐.eqv x) 𝓑.≅ 𝓑.eqv (f x)
   associate-comp : ∀ {x y z} (e₁ : x 𝓐.≃ y) (e₂ : y 𝓐.≃ z)
                  → ϕ x z (𝓐.concat e₁ e₂) 𝓑.≅ 𝓑.concat (ϕ x y e₁) (ϕ y z e₂)

  open Σ has-associate renaming (fst to 1-associate; snd to 2-associate) public
