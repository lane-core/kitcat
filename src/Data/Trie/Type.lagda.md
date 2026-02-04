The ternary finite set.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Trie.Type where

open import Core.Type

data Trie : Type where
  ll : Trie
  mm : Trie
  rr : Trie

```
