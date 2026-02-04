```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Core.Data.Pointed where

open import Core.Type
open import Core.Data.Sigma

Type* : ∀ u → Type (u ₊)
Type* u = Σ A ∶ Type u , A

instance
  Underlying-Pointed : ∀ {u} → Underlying (Type* u)
  Underlying-Pointed {u} .Underlying.ℓ-underlying = u
  Underlying-Pointed .Underlying.⌞_⌟ A = A .fst

```