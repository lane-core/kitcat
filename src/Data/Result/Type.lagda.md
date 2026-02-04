Dependent tagged pairs.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Result.Type where

open import Core.Type

data Res {u v} (A : Type u) (B : A -> Type v) : Type (u ⊔ v) where
  _#_ : (val : A) -> B val -> Res A B

```
