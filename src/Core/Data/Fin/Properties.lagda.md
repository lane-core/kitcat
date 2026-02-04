Finite types: path lemmas and discreteness proofs.

Definitions derived from: Data.Fin.Base, Data.Irr (Amelia Liao et al.; 1lab, January 2026)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Properties where

open import Core.Type
open import Core.Base
open import Core.Transport
open import Core.Data.Empty
open import Core.Data.Dec
open Dec
open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base

private variable
  m n k : Nat

```

## Path Lemmas

```agda

fin-path : {x y : Fin n} → x .lower ≡ y .lower → x ≡ y
fin-path {n = n} {x = fin _ ⦃ bounded = bx ⦄} {fin _ ⦃ bounded = by ⦄} p i =
  fin (p i) ⦃ is-prop→PathP (λ j → Irr-is-prop {A = p j Nat.< n}) bx by i ⦄

fsuc-inj : {i j : Fin n} → fsuc i ≡ fsuc j → i ≡ j
fsuc-inj p = fin-path (injS (ap lower p))
  where
    injS : S m ≡ S n → m ≡ n
    injS p = ap pred p
      where
        pred : Nat → Nat
        pred Z = Z
        pred (S n) = n

fzero≠fsuc : {i : Fin n} → ¬ (Path (Fin (S n)) fzero (fsuc i))
fzero≠fsuc p = ¬z≡s (ap lower p)
  where
    ¬z≡s : ∀ {n} → ¬ (Z ≡ S n)
    ¬z≡s q = subst f q tt
      where
        f : Nat → Type
        f Z = ⊤
        f (S _) = ⊥

absurd-fin : Fin Z → ⊥
absurd-fin i with fin-view i
... | ()

```

## Discreteness

Fin n is discrete (has decidable equality) and therefore a set.

```agda

Fin-discrete : (i j : Fin n) → Dec (i ≡ j)
Fin-discrete i j with Nat.DecEq-Nat (i .lower) (j .lower)
... | yes p = yes (fin-path p)
... | no ¬p = no λ q → ¬p (ap lower q)

Fin-is-set : is-set (Fin n)
Fin-is-set = hedberg Fin-discrete

```

## Weaken Equivalence

The view-based `weaken` from `Base` and the direct bound-manipulation version
are pointwise equal. Both preserve the underlying natural number, differing
only in how they construct the bound proof.

```agda

-- Direct bound-manipulation weaken (as in Monotone)
weaken-direct : Fin n → Fin (S n)
weaken-direct (fin k ⦃ bounded = forget p ⦄) = fin k ⦃ forget (Nat.step p) ⦄

-- The view-based weaken preserves lower
weaken-lower : (i : Fin n) → lower (weaken i) ≡ lower i
weaken-lower i with fin-view i
... | vz = refl
... | vs j = ap S (weaken-lower j)

-- The two weaken functions are pointwise equal
weaken≡weaken-direct : (i : Fin n) → weaken i ≡ weaken-direct i
weaken≡weaken-direct i = fin-path (weaken-lower i)

-- lower of the direct weaken is unchanged
lower-weaken : (j : Fin n) → lower (weaken-direct j) ≡ lower j
lower-weaken (fin k) = refl

-- lower of fsuc is successor
lower-fsuc : (j : Fin n) → lower (fsuc j) ≡ S (lower j)
lower-fsuc (fin k) = refl

```
