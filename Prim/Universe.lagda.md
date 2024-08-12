Lane Biocini
May 04, 2024

```
{-# OPTIONS --safe #-}

module Prim.Universe where

infixl -1 _type
infixl 70 _⁺⁺ _⁺⁺⁺

open import Agda.Primitive public
 renaming ( Set to infixl -1 Type
          ; SSet to infixl -1 SSet
          ; SSetω to SSetω
          ; Setω to 𝓤ω
          ; lzero to 𝓊₀
          ; lsuc to infixl 6 _⁺
          ; _⊔_ to infixl 6 _⊔_
          ) hiding (Prop) -- we work with the Univalent formulation of Prop

_type : ∀ 𝓊 → Type (𝓊 ⁺)
_type 𝓊 = Type 𝓊
{-# INLINE _type #-}
{-# DISPLAY Type 𝓊 = 𝓊 type #-}

_⁺⁺ : Level → Level
𝓊 ⁺⁺ = 𝓊 ⁺ ⁺

_⁺⁺⁺ : Level → Level
𝓊 ⁺⁺⁺ = 𝓊 ⁺ ⁺ ⁺

type-of : ∀ {𝓊} {X : 𝓊 type} (x : X) → 𝓊 type
type-of {𝓊} {X} = λ _ → X

level-of : ∀ {𝓊} (X : 𝓊 type) → Level
level-of {𝓊} X = 𝓊

𝓤₀ : 𝓊₀ ⁺ type
𝓤₀ = 𝓊₀ type
{-# DISPLAY 𝓊₀ type = 𝓤₀ #-}

𝓤₁ : 𝓊₀ ⁺⁺ type
𝓤₁ = 𝓊₀ ⁺ type

𝓤₂ : 𝓊₀ ⁺⁺⁺ type
𝓤₂ = 𝓊₀ ⁺⁺ type
