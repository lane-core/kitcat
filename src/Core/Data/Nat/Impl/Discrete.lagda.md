Discrete instance for Nat.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Nat.Impl.Discrete where

open import Core.Data.Nat.Type
open import Core.Trait.Eq
import Core.Data.Nat.Properties as NatP

instance
  Discrete-Nat : Discrete Nat
  Discrete-Nat .Discrete._≟_ = NatP.DecEq-Nat

```
