```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Nat.Order where

open import Lib.Core.Prim
open import Lib.Interval
open import Lib.Kan
open import Lib.Sigma

import Lib.HLevel as HLevel

open import Data.Path hiding (refl)

open Path
  hiding (refl)
  renaming (concat to infixl 40 _∙_)

import Data.Nat.Base as Nat
open Nat using (Nat; Z; S) renaming (add to _+_)

private variable
  u : Level
  @0 m n : Nat

infix 2 _<_

record _<_ (@0 m n : Nat) : Type where
  no-eta-equality
  field
    @0 offset : Nat
    instance @0 pf : S (offset + m) ≡ n

open _<_

<base : m < S m
<base .offset = Z
<base .pf = Path.refl

step : @0 m < n → m < S n
step p .offset = S (p .offset)
step p .pf i = S (p .pf i)

prop : is-prop (m < n)
prop {(m)} {(n)} f g i .offset =
 Nat.add.inj-right {f .offset} (λ k → Nat.pred ((f .pf ∙ sym (g . pf)) k)) i
prop {(m)} {(n)} f g i .pf =
  Path.HLevel.is-prop→PathP (λ i → Nat.set (S (φ i + m)) n) (f .pf) (g .pf) i
  where
  @0 φ : f .offset ≡ g .offset
  @0 φ = Nat.add.inj-right (λ i → Nat.pred ((f .pf ∙ sym (g . pf)) i))

data View {@0 m} : ∀ {@0 n} → @0 m < n → Type where
  vbase : View <base
  vstep : (f : m < n) → View f → View (step f)

view : ∀ {m n} (@0 f : m < n) → View f
view {(m)} {(Z)} f = ex-falso (Nat.pos-not-zero (f .offset + m) (f .pf))
view {(Z)} {S n} f = {!!}
view {S m} {S n} f = {!!}

infix 2 _≤_

_≤_ : Nat → Nat → Type
m ≤ n = m < S n

refl : ∀ {@0 n} → n ≤ n
refl .offset = Z
refl .pf = Path.refl

zero : ∀ {@0 n} → 0 ≤ n
zero {n} = {!!}

-- view : (f : m ≤ n) → View f
-- view {(Z)} {n} f = Path.erased-J (λ y p → View y) (view-base n) (prop (zero n) f)
-- view {S m} {(Z)} f = ex-falso (Nat.zero-not-pos (m + f .offset) (f .pf))
-- view {S m} {S n} f = {!!}

-- ind : (P : ∀ m → n ≤ m → Type u)
--     → (∀ k (q : n ≤ k) → P k q → P (S k) (suc q))
--     → P n refl
--     → (q : n ≤ m) → P m q
-- ind P s b q = {!!}
