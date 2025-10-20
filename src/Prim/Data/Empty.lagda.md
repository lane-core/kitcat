```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Data.Nat where

open import Prim.Type using ( Type )

import Agda.Builtin.Nat

module Nat where
  open Agda.Builtin.Nat public
    renaming ( suc to S
             ; zero to Z
             ; _<_ to _<₂_
             ; _+_ to add
             ; _*_ to mul
             ; _-_ to monus
             )
    hiding (module Nat)

  ind : ∀ {u} (P : @0 Nat → Type u)
      → (∀ (@0 k) → P k → P (S k))
      → P 0 → ∀ n → P n
  ind P s z Z = z
  ind P s z (S n) = s n (ind P s z n)

open Nat using (Nat; Z; S) public

module ≤ℕ where
  infix 7 _≤_ _<_

  data _≤_ : Nat → Nat → Type where
    instance 0≤ : ∀ {n} → Z ≤ n
    s≤s : ∀ {x y} → x ≤ y → S x ≤ S y

  open _≤_ public

  _<_ : Nat → Nat → Type
  m < n = S m ≤ n

  instance
    0< : ∀ {n} → Z < S n
    0< = s≤s 0≤

  ≤S : ∀ {m n} → m ≤ n → m ≤ (S n)
  ≤S 0≤ = 0≤
  ≤S (s≤s p) = s≤s (≤S p)

  ≤inj : ∀ {m n} → S m ≤ S n → m ≤ n
  ≤inj (s≤s p) = p
