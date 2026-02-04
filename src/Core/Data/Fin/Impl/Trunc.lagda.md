Trunc instance for Fin.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Impl.Trunc where

open import Core.Data.Nat.Type
open import Core.Data.Fin.Type
open import Core.Trait.Trunc
import Core.Data.Fin.Properties as FinP

private variable
  n : Nat

instance
  Trunc-Fin : ∀ {k} → Trunc (Fin n) (S (S k))
  Trunc-Fin = set-trunc FinP.Fin-is-set

{-# OVERLAPS Trunc-Fin #-}

```
