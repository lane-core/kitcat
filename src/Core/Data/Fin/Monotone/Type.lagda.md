Order-preserving maps between finite types — type definitions.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Monotone.Type where

open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Sum
open import Core.Type
open import Core.Base

open Nat

private variable
  m n k l : Nat


```

## Ordering on Fin

We lift the ordering from natural numbers to finite types via
the underlying `lower` field. The exported ordering is propositional
(wrapped in `Irr`) to ensure that ordering predicates are proof-irrelevant.

```agda

_<ᶠ_ : Fin n → Fin n → Type
i <ᶠ j = Irr (lower i < lower j)

_≤ᶠ_ : Fin n → Fin n → Type
i ≤ᶠ j = Irr (lower i ≤ lower j)

infix 4 _<ᶠ_ _≤ᶠ_

```

## Ordering lemmas

Basic properties of the lifted ordering.

```agda

≤ᶠ-refl : (i : Fin n) → i ≤ᶠ i
≤ᶠ-refl i = forget le.rx

≤ᶠ-trans : {i j k : Fin n} → i ≤ᶠ j → j ≤ᶠ k → i ≤ᶠ k
≤ᶠ-trans (forget p) (forget q) = forget (le.cat p q)


```

## Comparison View

A decision procedure for comparing elements of `Fin n`. The result is
a sum type: either `i ≤ j` or `j < i`.

```agda

-- Compare two Fin elements (same index)
fin-compare : (i j : Fin n) → i ≤ᶠ j ⊎ j <ᶠ i
fin-compare i j with cmp (lower i) (lower j)
... | inl p = inl (forget p)
... | inr q = inr (forget q)

```

## Bound-Transforming Operations

These operations transform a `Fin n` to a `Fin (S n)` by directly
manipulating the bound proof.

```agda

-- Keep the same lower value, weaken the bound: k < n implies k < S n
-- Named `weaken` following SSet conventions (pairs with `fsuc`)
weaken : Fin n → Fin (S n)
weaken (fin k ⦃ bounded = forget p ⦄) = fin k ⦃ forget (step p) ⦄

-- Predecessor on Fin: requires evidence that the value is positive
fpred : (j : Fin (S n)) → Z < lower j → Fin n
fpred {n} (fin (S k) ⦃ bounded = forget p ⦄) _ = fin k ⦃ forget (lt.peel n p) ⦄

-- Restrict Fin (S n) to Fin n: requires evidence that value is small enough
restrict : (i : Fin (S n)) → lower i < n → Fin n
restrict (fin k) p = fin k ⦃ forget p ⦄

```

## Monotonicity predicate

A function between finite types is monotone if it preserves the
ordering. Since the ordering is propositional (via `Irr`), the
monotonicity predicate is also propositional.

```agda

is-monotone : (Fin m → Fin n) → Type
is-monotone f = ∀ i j → i ≤ᶠ j → f i ≤ᶠ f j

```

## Bundled monotone maps

```agda

record _⇒_ (m n : Nat) : Type where
  no-eta-equality
  field
    map : Fin m → Fin n
    @0 has-is-monotone : is-monotone map

open _⇒_ public

infix 5 _⇒_

```
