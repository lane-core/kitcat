Snoc lists: lists built by appending to the right.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.SnocList.Type where

open import Core.Type

data SnocList {u} (A : Type u) : Type u where
  []   : SnocList A
  _∶<_ : SnocList A -> A -> SnocList A

```
