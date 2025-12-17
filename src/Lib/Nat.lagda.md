```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Nat where

open import Lib.Core.Prim

import Agda.Builtin.Nat

private variable
  u : Level
  m n : Agda.Builtin.Nat.Nat

module Nat = Agda.Builtin.Nat
  renaming ( suc to S
           ; zero to Z
           ; _<_ to _<₂_
           ; _+_ to add
           ; _*_ to mul
           ; _-_ to monus
           )
  hiding (module Nat)
open Nat using (Nat; Z; S) public

module IndOrd where
  data _<_ (m : Nat) : Nat → Type where
    instance Suc : m < S m
    Step : m < n → m < S n

  open _<_ public

  _≤_ : Nat → Nat → Type
  m ≤ n = m < S n

  instance
    0< : Z < S n
    0< {n = Z} = Suc
    0< {n = S n} = Step 0<

  !n<z : ∀ {n} → ¬ (n < Z)
  !n<z {n} ()

  wconst : m < n → n < Z → m < Z
  wconst p q = ex-falso (!n<z q)

  trans : ∀ {k} → m < n → n < k → m < k
  trans {k = Z} = wconst
  trans {k = S k} p Suc = Step p
  trans {k = S k} p (Step q) = Step (trans p q)

  refl : n ≤ n
  refl = Suc

  ind : (P : ∀ m → n < m → Type u)
      → (∀ k (q : n < k) → P k q → P (S k) (Step q))
      → (c : P (S n) Suc)
      → (q : n < m) → P m q
  ind {n = k} {m = S n} P acc c Suc = c
  ind {n = k} {m = S n} P acc c (Step q) = acc n q (ind P acc c q)

  record Acc {u v} {A : Type u} (_<_ : A → A → Type v) (x : A) : Type (u ⊔ v) where
    constructor mkAcc
    inductive
    field
      @0 acc : ((y : A) → y < x → Acc _<_ y)

  open Acc public

  @0 wf : ∀ n → Acc _<_ n
  wf Z .acc y f = ex-falso (!n<z f)
  wf (S n) .acc y Suc = wf n
  wf (S n) .acc y (Step f) = wf n .acc y f

  rec : (P : Nat → Type u)
    → (∀ n → (∀ m → m < n → P m) → P n)
    → ∀ n → P n
  rec P step = go
    where
    go : ∀ n → P n
    gone : ∀ n m → m < n → P m

    go Z = step Z (λ m f → ex-falso (!n<z f))
    go (S n) = step (S n) (gone (S n))

    gone (S n) m Suc = go n
    gone (S n) m (Step p) = gone n m p

ind : (P : Nat → Type u)
  → (∀ k → P k → P (S k))
  → P 0 → ∀ n → P n
ind P s z Z = z
ind P s z (S n) = s n (ind P s z n)
