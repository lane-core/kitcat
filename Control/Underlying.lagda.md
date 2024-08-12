Lane Biocini
August 1st, 2024

```agda

{-# OPTIONS --safe #-}

module Control.Underlying where

open import Prim.Universe

-- Notation class for types which have a chosen projection into a
-- universe, i.e. a preferred "underlying type".
record Underlying {𝓊} (A : 𝓊 type) : 𝓤ω where
  field
    ℓ : Level
    ⌞_⌟ : A → ℓ type

open Underlying ⦃ ... ⦄ public

underlying-fam : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : A → 𝓋 type}
             → {x : A} → Underlying (B x)
underlying-fam {𝓊} .Underlying.ℓ = 𝓊
underlying-fam {𝓊} {𝓋} {A} .⌞_⌟ p = A

record Underlyingω (A : 𝓤ω) : 𝓤ω where
 field
  ℓ : Level
  ⌞_⌟ : A → ℓ type

open Underlyingω ⦃ ... ⦄ public
