Binary strings: the free type on two generators.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Bin.Type where

open import Core.Type

data Bin : Type where
  []  : Bin
  ll : Bin → Bin
  rr : Bin → Bin

```
