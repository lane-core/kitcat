W-types: well-founded trees.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.W.Type where

open import Core.Type

data W {u v} (A : Type u) (B : A -> Type v) : Type (u ⊔ v) where
  sup : (a : A) -> (B a -> W A B) -> W A B

```
