Trunc instance for Nat.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Nat.Impl.Trunc where

open import Core.Data.Nat.Type
open import Core.Trait.Trunc
import Core.Data.Nat.Properties as NatP

instance
  Trunc-Nat : ∀ {k} → Trunc Nat (S (S k))
  Trunc-Nat = set-trunc NatP.set

{-# OVERLAPS Trunc-Nat #-}

```
