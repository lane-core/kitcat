Finite types: views, conversion, and weakening operations.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Base where

open import Core.Type
open import Core.Data.Nat
open import Core.Data.Fin.Type

open Nat
  renaming (_+_ to _+N_; _*_ to _*N_)

private variable
  m n k : Nat

```

## View for Pattern Matching

```agda

data Fin-view : Fin n → Type where
  vz : Fin-view {S n} fzero
  vs : (i : Fin n) → Fin-view {S n} (fsuc i)

fin-view : (i : Fin n) → Fin-view i
fin-view {n = S n} (fin Z) = vz
fin-view {n = S n} (fin (S k) ⦃ bounded = forget p ⦄) = vs (fin k ⦃ forget (Nat.lt.peel n p) ⦄)
fin-view {n = Z} (fin _ ⦃ bounded = forget () ⦄)

```

## Conversion to Nat

```agda

toNat : Fin n → Nat
toNat = lower

```

## Last element

The maximum element of `Fin (S n)`.

```agda

flast : Fin (S n)
flast {n} = fin n ⦃ forget suc ⦄

```

## Weakening and Strengthening

```agda

weaken : Fin n → Fin (S n)
weaken i with fin-view i
... | vz = fzero
... | vs j = fsuc (weaken j)

inject : m Nat.≤ n → Fin m → Fin n
inject q (fin k ⦃ bounded = forget p ⦄) = fin k ⦃ forget (Nat.lt-le-cat p q) ⦄

-- Inject into higher positions: Fin n → Fin (m + n)
-- This places the element in the "upper" part of the sum
raise : ∀ m {n} → Fin n → Fin (m +N n)
raise Z i = i
raise (S m) i = fsuc (raise m i)

```
