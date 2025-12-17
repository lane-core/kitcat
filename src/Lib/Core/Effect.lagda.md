This design pattern is lifted from 1Lab's version of this module

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Interface.Effect where

open import Lib.Core.Prim

record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀ : ∀ {ℓ} → Type ℓ → Type (adj ℓ)
