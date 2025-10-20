```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Nat.Order where

open import Prim.Type
open import Prim.Interval
open import Prim.Kan
open import Prim.Data.Sigma

import Prim.Path as Path
open Path
  using (_≡_; PathP; Square; idtofun; sym; ap; is-prop; is-set)
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

base : m < S m
base .offset = Z
base .pf = Path.refl

step : @0 m < n → m < S n
step p .offset = S (p .offset)
step p .pf i = S (p .pf i)

prop : is-prop (m < n)
prop {(m)} {(n)} f g i .offset =
  Nat.add.inj-right {f .offset} (λ k → Nat.pred ((f .pf ∙ sym (g . pf)) k)) i
prop {(m)} {(n)} f g i .pf =
  Path.is-prop→PathP (λ i → Nat.set (S (φ i + m)) n) (f .pf) (g .pf) i
  where
  @0 φ : f .offset ≡ g .offset
  @0 φ = Nat.add.inj-right (λ i → Nat.pred ((f .pf ∙ sym (g . pf)) i))

data View {@0 m} : ∀ {@0 n} → @0 m < n → Type where
  vbase : View base
  vstep : (f : m < n) → View f → View (step f)

view : ∀ {m n} (@0 f : m < n) → View f
view {(m)} {(Z)} f = ex-falso (Nat.pos-not-zero (f .offset + m) (f .pf))
view {(Z)} {S n} f = {!!}
view {S m} {S n} f = {!!}

```
infix 2 _≤_
record _≤_ (@0 m n : Nat) : Type where
  constructor ltNat
  field
    @0 offset : Nat
    @0 pf : n ≡ m + offset

open _≤_
_<_ : Nat → Nat → Type
m < n = S m ≤ n

refl : ∀ {@0 n} → n ≤ n
refl .offset = Z
refl {n = Z} .pf = λ _ → Z
refl {n = S n} .pf = λ i → S (refl {n = n} .pf i)

zero : ∀ {@0 n} → 0 ≤ n
zero {n} = ltNat n Path.refl

add : ∀ {@0 n k} → @0 m ≤ n → m ≤ (n + k)
add {k} p .offset = p .offset + k
add {m} {k} p .pf = ap (_+ k) (p .pf) ∙ sym (Nat.assoc m (p .offset) k)

suc : @0 n ≤ m → n ≤ S m
suc f .offset = S (f .offset)
suc {(Z)} f .pf = ap S (f .pf)
suc {S n} f .pf = ap S (f .pf) ∙ ap S (Nat.rsuc n (f .offset))

prop : is-prop (m ≤ n)
prop {m} {n} (ltNat a p) (ltNat b q) i =
  ltNat (φ i) (Path.is-prop→PathP (λ i → Nat.set n (m + φ i)) p q i) where
    @0 φ : a ≡ b
    @0 φ = Nat.add.inj-left (Path.concat2 (sym p) Path.refl q)

data View {@0 m} : ∀ {@0 n} → @0 m ≤ n → Type where
  vrefl : View refl
  vsuc : (f : m ≤ n) → View f → View (suc f)

view-zero : ∀ n → View (zero {n})
view-zero Z = vrefl
view-zero (S n) = vsuc (zero) (view-zero n)

le-zero : ∀ {m} → @0 m ≤ Z → Z ≡ m
le-zero {(Z)} q = λ _ → Z
le-zero {S m} q = ex-falso (Nat.zero-not-pos (m + q .offset) (q . pf))

view-base : ∀ {@0 m} (@0 f : m ≤ Z) → View f
view-base {m} (ltNat k p) = idtofun φ vrefl where
  @0 ψ : Z ≡ m
  @0 ψ = le-zero (ltNat k p)

  @0 α : Z ≡ k
  @0 α = ψ ∙ Nat.add.to-zero p

  @0 β : PathP (λ i → Z ≡ ψ i + α i) Path.refl p
  @0 β = Path.is-prop→PathP (λ i → Nat.set Z (ψ i + α i)) Path.refl p

  φ : View (ltNat Z (λ _ → Z)) ≡ View (ltNat k p)
  φ i = View {ψ i} {Z} (ltNat (α i) (β i))

view-suc : ∀ {n} (@0 f : S m ≤ n) → View f
view-suc {m} {n} f = {!!}

view : ∀ {m n} (@0 f : m ≤ n) → View f
view {m} {(Z)} f = view-base f
view {(Z)} {S n} f = Path.erased-J (λ y q → View y) (view-zero (S n)) (prop zero f)
view {S m} {S n} (ltNat offset₁ pf₁) = {!!} where
  test : {!!} ≤ {!!}
  test = {!!}

-- view : (f : m ≤ n) → View f
-- view {(Z)} {n} f = Path.erased-J (λ y p → View y) (view-base n) (prop (zero n) f)
-- view {S m} {(Z)} f = ex-falso (Nat.zero-not-pos (m + f .offset) (f .pf))
-- view {S m} {S n} f = {!!}

ind : (P : ∀ m → n ≤ m → Type u)
    → (∀ k (q : n ≤ k) → P k q → P (S k) (suc q))
    → P n refl
    → (q : n ≤ m) → P m q
ind P s b (ltNat offset pf) = {!!}
