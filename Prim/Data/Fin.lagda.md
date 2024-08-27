Lane Biocini
March 30st, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Data.Fin where

open import Prim.Universe
open import Prim.Data.Nat renaming (add to _+_)
open import Prim.Pi
open import Global.Cut

data Fin : Nat → Type where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → (i : Fin n) → Fin (suc n)

nat-to-fin : (n : Nat) → Fin (suc n)
nat-to-fin zero = zero
nat-to-fin (suc n) = suc (nat-to-fin n)

zero-elim : ∀ {𝓋} {A : 𝓋 type} → Fin 0 → A
zero-elim ()
