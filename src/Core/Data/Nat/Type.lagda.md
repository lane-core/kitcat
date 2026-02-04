Natural numbers: type, arithmetic, and ordering.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Nat.Type where

open import Core.Type

open import Agda.Builtin.Nat public
  using (Nat)
  renaming ( zero to Z
           ; suc to S )
  hiding (module Nat)
