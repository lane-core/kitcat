Disjoint union (coproduct).

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Sum.Type where

open import Core.Type

data _⊎_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr -1 _⊎_

```
