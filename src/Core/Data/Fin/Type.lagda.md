Finite types: type definition and constructors.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Fin.Type where

open import Core.Type
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base

```

## Finite Sets

The type `Fin n` has exactly `n` elements. We define it as a record
containing a natural number with an irrelevant proof that it's bounded.
This gives good computational behavior: `subst Fin p x` computes definitionally.

Per 1lab.

```agda

record Fin (n : Nat) : Type where
  constructor fin
  field
    lower : Nat
    ⦃ bounded ⦄ : Irr (lower < n)

open Fin public

private variable
  m n k : Nat

```

## Constructors

```agda

pattern fzero = fin Z

fsuc : Fin n -> Fin (S n)
fsuc (fin k ⦃ bounded = forget p ⦄) = fin (S k) ⦃ forget (s<s p) ⦄

```
