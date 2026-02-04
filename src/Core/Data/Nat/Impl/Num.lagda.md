Num instance for Nat.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Nat.Impl.Num where

open import Core.Data.Nat.Type
import Core.Data.Nat.Base as Nat
open import Core.Trait.Num

instance
  Num-Nat : Num Nat
  Num-Nat ._+_ = Nat._+_
  Num-Nat ._*_ = Nat._*_
  Num-Nat .fromInteger = Int.to-nat

```
