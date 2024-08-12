Lane Biocini
August 6, 2024

The Decidable type

```agda

{-# OPTIONS --safe #-}

module Prim.Dec where

open import Prim.Universe
open import Prim.Empty

data Dec {𝓊} (A : 𝓊 type) : 𝓊 type where
 yes : (a : A) → Dec A
 no : (na : ¬ A) → Dec A

dec-induction : ∀ {𝓊 𝓋} {A : 𝓊 type} (B : Dec A → 𝓋 type)
    → (∀ a → B (yes a))
    → (∀ na → B (no na))
    → (c : Dec A) → B c
dec-induction B f g (yes a) = f a
dec-induction B f g (no na) = g na
