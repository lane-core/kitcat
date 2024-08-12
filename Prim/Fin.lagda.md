Lane Biocini
March 30st, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Fin where

open import Prim.Universe
open import Prim.Nat public

data Fin : Nat → 𝓤₀ where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → (i : Fin n) → Fin (suc n)

nat-to-fin : (n : Nat) → Fin (suc n)
nat-to-fin zero = zero
nat-to-fin (suc n) = suc (nat-to-fin n)

instance
 numeral-nat : ∀ {n : Nat} → Numeral (Fin (suc n))
 numeral-nat .is-pos = Fin
 numeral-nat {n} .Numeral.from-nat k ⦃ j ⦄ = nat-to-fin n
