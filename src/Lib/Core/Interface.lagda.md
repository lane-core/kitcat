```
{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Interface where

open import Lib.Core.Prim

record Interface {u v l₀ l₁} {S : Type u} {T : Type v}
  (src : S → Type l₀) -- source specification
  (tgt : T → Type l₁) -- target specification
  (a : S) (b : T)
  : Typeω
  where
  no-eta-equality
  field
    intr : src a → tgt b
