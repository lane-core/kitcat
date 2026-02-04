Polymorphic binary trees: the free magma on A.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Tree.Type where

open import Core.Type

data Tree {u} (A : Type u) : Type u where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

```
