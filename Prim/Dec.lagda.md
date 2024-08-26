Lane Biocini
August 6, 2024

The Decidable Type

```agda

{-# OPTIONS --safe #-}

module Prim.Dec where

open import Prim.Universe
open import Prim.Empty using (¬_)

data Dec {𝓊} (A : 𝓊 type) : 𝓊 type where
 yes : (a : A) → Dec A
 no : (na : ¬ A) → Dec A

ind : ∀ {𝓊 𝓋} {A : 𝓊 type} (B : Dec A → 𝓋 type)
    → (∀ a → B (yes a))
    → (∀ na → B (no na))
    → (c : Dec A) → B c
ind B f g (yes a) = f a
ind B f g (no na) = g na
