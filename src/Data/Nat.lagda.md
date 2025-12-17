```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Nat where

open import Lib.Core.Prim
open import Lib.Core.Base

import Lib.Path as Path
open Path
  using (idtofun; hsym; ap; is-set)

open import Lib.Path.Gpd
  using ()
  renaming (cat to infixl 40 _∙_)

open import Data.Dec
import Lib.Nat as N

open N using (Nat; S; Z) public

private variable
  u : Level
  m n : Nat

```
module Nat where
  open N public
  open N using () renaming (add to _+_)



  assoc : ∀ m n k → m + (n + k) ≡ m + n + k
  assoc m n k = {!!}

private module M where
  open Nat using () renaming (add to _+_)
  infix 2 _≤_
  record _≤_ (m n : Nat) : Type where
    constructor mkOrd
    field
      offset : Nat
      @0 pf : n ≡ m + offset

  open _≤_
  _<_ : Nat → Nat → Type
  m < n = S m ≤ n

  refl : n ≤ n
  refl .offset = Z
  refl {n = Z} .pf = λ _ → Z
  refl {n = S n} .pf = λ i → S (refl {n = n} .pf i)

  zero : 0 ≤ n
  zero {n = Z} = refl
  zero {n = S n} .offset = S n
  zero {n = S n} .pf = λ _ → S n

  add : ∀ {n k} → m ≤ n → m ≤ (n + k)
  add {k} p .offset = p .offset + k
  add {k} p .pf = {!p .pf!}

  suc : n ≤ m → n ≤ S m
  suc {m = m} p .offset = S (p .offset)
  suc {n = Z} p .pf = λ i → S (p .pf i)
  suc {n = S n} {m = m} p .pf = λ i → S {!!}

  data View {m : Nat} : m ≤ n → Type where
    vrefl : View refl
    vsuc : (f : m ≤ n) → View f → View (suc f)

  view : (f : m ≤ n) → View f
  view {m = Z} {n = Z} (mkOrd k q) = {!!}
  view {m = Z} {n = S n} (mkOrd k q) = {!!}
  view {m = S m} {n = n} (mkOrd k q) = {!!}

  step : n ≤ m → n ≤ S m
  step {n = n} p .offset = S (p .offset)
  step (mkOrd offset pf) .pf = {!!}

  ind : (P : ∀ m → n ≤ m → Type u)
      → (∀ k (q : n ≤ k) → P k q → P (S k) (step q))
      → P n refl
      → (q : n ≤ m) → P m q
  ind P s b (mkOrd offset pf) = {!!}


private
    f : Nat → Type
    f Z = ⊥
    f (S n) = ⊤

pred : Nat → Nat
pred Z = Z
pred (S n) = n

zero-not-pos : ∀ n → ¬ (Z ≡ S n)
zero-not-pos n p = idtofun (ap f (sym p)) tt

pos-not-zero : ∀ n → ¬ (S n ≡ Z)
pos-not-zero n p = idtofun (ap f p) tt

Nat-finite : ∀ n → ¬ (n ≡ S n)
Nat-finite Z = zero-not-pos Z
Nat-finite (S n) p = Nat-finite n (ap pred p)

injS : ∀ {m} {n} → S m ≡ S n → m ≡ n
injS p = ap pred p

DecEq-Nat : DecEq Nat
DecEq-Nat Z Z = yes (λ _ → Z)
DecEq-Nat Z (S y) = no (zero-not-pos y)
DecEq-Nat (S x) Z = no (pos-not-zero x)
DecEq-Nat (S x) (S y) = φ (DecEq-Nat x y) where
  φ : Dec (x ≡ y) → Dec (S x ≡ S y)
  φ (yes p) = yes (ap S p)
  φ (no p) = no λ q → p (ap pred q)

is-set-Nat : is-set Nat
is-set-Nat = hedberg DecEq-Nat

