Truncation level instance for propositional truncation.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Trunc.Properties where

open import Core.Type
open import Core.Data.Trunc.Type
open import Core.Data.Trunc.Base
open import Core.Trait.Trunc using (Trunc; prop-trunc)
open import Core.Data.Nat using (Nat; S)

private variable
  ℓ : Level

instance
  Trunc-∥∥ : {A : Type ℓ} {k : Nat} → Trunc ∥ A ∥ (S k)
  Trunc-∥∥ = prop-trunc squash

```
