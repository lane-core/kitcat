Propositional truncation as a higher inductive type.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Trunc.Type where

open import Core.Type
open import Core.Base using (_≡_)

private variable
  ℓ : Level

data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

infix 5 ∥_∥

```
