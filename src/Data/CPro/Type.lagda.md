A mutually inductive type which generates the product of cyclic groups

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.CPro.Type where

open import Core.Base using (_≡_; refl)
open import Core.Type using (Type; 0ℓ)
open import Core.Data.Fin

module CPro {u} (A : Type u) where
  data L : Type 0ℓ
  data R : Type 0ℓ

  data L where
    e₀    : L
    e₁    : L
    cross : R → L

  data R where
    step : R-sgn → L → R-edge
