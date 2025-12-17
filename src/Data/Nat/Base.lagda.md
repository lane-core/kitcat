```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Nat.Base where

open import Lib.Core.Prim
open import Lib.Interval

import Lib.Path as Path
open Path
  using (_≡_; idtofun; sym; ap; is-set)
  renaming (concat to infixl 40 _∙_)

open import Data.Dec
import Lib.Nat as N

open N using (Nat; S; Z) renaming (add to _+_)

private variable
  u : Level
  @0 m n : Nat

assoc : ∀ m n k → m + (n + k) ≡ m + n + k
assoc Z n k = Path.refl
assoc (S m) n k = ap S (assoc m n k)

rsuc : ∀ m n → S (m + n) ≡ m + S n
rsuc Z n = Path.refl
rsuc (S m) n = ap S (rsuc m n)

private
  code : Nat → Type
  code Z = ⊥
  code (S n) = ⊤

pred : Nat → Nat
pred Z = Z
pred (S n) = n

zero-not-pos : ∀ n → ¬ (Z ≡ S n)
zero-not-pos n p = idtofun (ap code (sym p)) tt

pos-not-zero : ∀ n → ¬ (S n ≡ Z)
pos-not-zero n p = idtofun (ap code p) tt

no-succ-fp : ∀ n → ¬ (n ≡ S n)
no-succ-fp Z = zero-not-pos Z
no-succ-fp (S n) p = no-succ-fp n (ap pred p)

inj-succ : ∀ {@0 m n} → S m ≡ S n → m ≡ n
inj-succ p i = pred (p i)

zero-right : ∀ m → m ≡ m + Z
zero-right Z = Path.refl
zero-right (S m) = ap S (zero-right m)

module add where
  inj-left : ∀ {k} → k + m ≡ k + n → m ≡ n
  inj-left {k = Z} = id
  inj-left {k = S k} p = inj-left (inj-succ p)

  inj-right : ∀ {m n k} → m + k ≡ n + k → m ≡ n
  inj-right {m} {n} {k = Z} p =
    Path.concat2 (zero-right m) p (sym (zero-right n))
  inj-right {m} {n} {k = S k} p = inj-right λ i → pred (φ i) where
    φ : S (m + k) ≡ S (n + k)
    φ i = Path.concat2 (rsuc m k) p (sym (rsuc n k)) i

  to-zero : ∀ {m} {@0 n} → Z ≡ m + n → m ≡ n
  to-zero {m = Z} p = p
  to-zero {m = S m} {n} p = ex-falso (zero-not-pos (m + n) p)

dec-eq : DecEq Nat
dec-eq Z Z = yes (λ _ → Z)
dec-eq Z (S y) = no (zero-not-pos y)
dec-eq (S x) Z = no (pos-not-zero x)
dec-eq (S x) (S y) = φ (dec-eq x y) where
  φ : Dec (x ≡ y) → Dec (S x ≡ S y)
  φ (yes p) = yes (ap S p)
  φ (no p) = no λ q → p (ap pred q)

set : is-set Nat
set = hedberg dec-eq

open N public
