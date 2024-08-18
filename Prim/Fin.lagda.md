Lane Biocini
March 30st, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Fin where

open import Prim.Universe
open import Prim.Nat renaming (add to _+_)
open import Prim.Pi
open import Global.Cut
open import Prim.Plus

data Fin : Nat → Type where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → (i : Fin n) → Fin (suc n)

nat-to-fin : (n : Nat) → Fin (suc n)
nat-to-fin zero = zero
nat-to-fin (suc n) = suc (nat-to-fin n)

zero-elim : ∀ {𝓋} {A : 𝓋 type} → Fin 0 → A
zero-elim ()

infixr 6 _⊸_
_⊸_ : Nat → Nat → Type
m ⊸ n = Fin m → Fin n

trn : ∀ {p q} → suc p ⊸ q → p ⊸ q
trn F = λ x → F (suc x)

-- par : ∀ {p p' q q'} → p ⊸ q → p' ⊸ q' + q → (p + p') ⊸ (q + q')
-- par {zero} {zero} f g = zero-elim
-- par {zero} {suc p'} {zero} f g = g
-- par {zero} {suc p'} {suc q} {zero} f g = zero-elim (g zero)
-- par {zero} {suc p'} {suc q} {suc q'} f g = {!!}
-- par {suc p} f g = {!!}
