Lane Biocini
August 1st, 2024

This was directly inspired by 1lab's equivalent. This typeclass controls a
projection function that sends any term to a chosen underlying type. This is
useful in the case that you have more complex constructors containing a type
which you will primarily be operating upon in developing the theory.
Lane Biocini
August 17th 2024

1lab's approach is simple, with ergonomic polymorphism utilizing 𝓤ω.
Thank you 1lab.

```agda

{-# OPTIONS --safe #-}

module Global.Underlying where

open import Prim.Universe

-- Notation class for types which have a chosen projection into a
-- universe, i.e. a preferred "underlying type".

record Underlying {𝓊} (A : 𝓊 type) : 𝓤ω where
  field
    ℓ : Level
    ⌞_⌟ : A → ℓ type

open Underlying ⦃ ... ⦄ hiding (ℓ) public

underlying-fam : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : A → 𝓋 type}
             → {x : A} → Underlying (B x)
underlying-fam {𝓊} .Underlying.ℓ = 𝓊
underlying-fam {𝓊} {𝓋} {A} .⌞_⌟ p = A
