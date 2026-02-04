Natural numbers: type, arithmetic, and ordering.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Nat where

open import Core.Type
open import Core.Data.Nat.Type public

module Nat where
  open import Core.Data.Nat.Base public
  open import Core.Data.Nat.Properties public

  module impl where
    open import Core.Data.Nat.Impl.Num public
    open import Core.Data.Nat.Impl.Show public
    open import Core.Data.Nat.Impl.Discrete public
    open import Core.Data.Nat.Impl.Trunc public
