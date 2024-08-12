Lane Biocini
March 27st, 2024

```agda
{-# OPTIONS --safe #-}

module Prim.Unit where

open import Prim.Universe

record 𝟙 {𝓊} : 𝓊 type where instance constructor ⋆

open 𝟙 {{...}} public

⊤ : 𝓤₀
⊤ = 𝟙
{-# BUILTIN UNIT ⊤ #-}

unit-induction : ∀ {𝓊} {P : ⊤ → 𝓊 type}
    → P ⋆
    → (x : ⊤) → P x
unit-induction b = λ _ → b
