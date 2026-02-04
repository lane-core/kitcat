The Catalan simplicial set: strict interval-closed relations.

An n-simplex of K is a strict, interval-closed binary relation on
`Fin (S n)`. Face maps act by precomposition with the coface injection
sigma from `Fin.Monotone`. This gives a presheaf on Delta whose 0-cells
are points, 1-cells are ordered pairs, and 2-cells are triangles.

This module uses `--cubical` (not `--erased-cubical`) because K-path
requires propositional extensionality (`propext`), which depends on `ua`.

Credit: Lack-Street, "The formal theory of monads II"

```agda

{-# OPTIONS --cubical --safe --no-guardedness #-}

module Lib.SSet.Catalan.Base where

open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_)
open import Core.Transport
  using (is-prop→PathP; is-prop→SquareP)
open import Core.Function.Embedding
  using (_↪_; _∙↪_; Emb-is-prop; embedding→is-prop)
open import Core.Equiv using (_≃_; is-equiv; equiv; is-equiv-is-prop)
open import Core.Univalence
  using (ua; ua-η; idtoeqv)
open import Core.Set using (propext; Type-path-is-prop)
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base
open import Core.Data.Fin.Properties
open import Core.Data.Fin.Monotone
open import Core.Trait.Trunc
  using (Π-is-prop; Πi-is-prop; ×-is-hlevel)

open Nat

private variable
  u : Level
  n : Nat

```

## The K record

An n-simplex of the Catalan simplicial set is a strict,
interval-closed binary relation on `Fin (S n)`. Strictness means
`R i j` embeds into `i < j`. Interval-closure means any related pair
`R i k` with an intermediate `j` decomposes into `R i j` and
`R j k`. Propositionality of `R` is derived from the embedding into
the proposition `i <ᶠ j`.

```agda

record K (u : Level) (n : Nat) : Type (u ₊) where
  no-eta-equality
  field
    R : Fin (S n) → Fin (S n) → Type u
    strict : ∀ {i j} → R i j ↪ (i <ᶠ j)
    closed
      : ∀ {i j k} → i <ᶠ j → j <ᶠ k
      → R i k → R i j × R j k

  prop : ∀ i j → is-prop (R i j)
  prop i j = embedding→is-prop (strict .snd) Irr-is-prop

open K

{-# INLINE K.constructor #-}

```

## Paths in K

Two K values are equal when their R fields agree pointwise. Since
each `R i j` is propositional (via the embedding into `_<ᶠ_`),
bi-implication suffices to build a path in `Type` via `propext`, and
the remaining fields are propositional so their `PathP` proofs are
automatic.

```agda

private
  strict-type-is-prop
    : (R : Fin (S n) → Fin (S n) → Type u)
    → is-prop (∀ {i j} → R i j ↪ (i <ᶠ j))
  strict-type-is-prop R =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Emb-is-prop Irr-is-prop

  closed-type-is-prop
    : (R : Fin (S n) → Fin (S n) → Type u)
    → (Rp : ∀ i j → is-prop (R i j))
    → is-prop (∀ {i j k} → i <ᶠ j → j <ᶠ k
      → R i k → R i j × R j k)
  closed-type-is-prop R Rp =
    Πi-is-prop λ _ → Πi-is-prop λ _ →
      Πi-is-prop λ _ → Π-is-prop λ _ → Π-is-prop λ _ →
        Π-is-prop λ _ → ×-is-hlevel 1 (Rp _ _) (Rp _ _)

```

Build a path between two K values from pointwise bi-implication of
their R fields. The remaining fields are propositional and fill via
`is-prop→PathP`.

```agda

K-path
  : {k₁ k₂ : K u n}
  → (fwd : ∀ i j → R k₁ i j → R k₂ i j)
  → (bwd : ∀ i j → R k₂ i j → R k₁ i j)
  → k₁ ≡ k₂
K-path {k₁ = k₁} {k₂} fwd bwd i .R a b =
  propext (prop k₁ a b) (prop k₂ a b)
    (fwd a b) (bwd a b) i
K-path {k₁ = k₁} {k₂} fwd bwd i .strict =
  is-prop→PathP
    (λ i → strict-type-is-prop
      (K-path {k₁ = k₁} {k₂} fwd bwd i .R))
    (strict k₁) (strict k₂) i
K-path {k₁ = k₁} {k₂} fwd bwd i .closed lt₁ lt₂ r =
  is-prop→PathP
    (λ i → closed-type-is-prop
      (K-path {k₁ = k₁} {k₂} fwd bwd i .R)
      (λ a b → embedding→is-prop
        (K-path {k₁ = k₁} {k₂} fwd bwd i .strict .snd)
        Irr-is-prop))
    (closed k₁) (closed k₂) i lt₁ lt₂ r

```

## K is a set

Paths in K are determined by pointwise paths `R k₁ i j = R k₂ i j`,
each of which is propositional (by `Type-path-is-prop`). The remaining
fields are propositional, so their PathP proofs are unique. Hence K
paths are propositional, making K a set.

```agda

K-is-set : ∀ {u n} → is-set (K u n)
K-is-set k₁ k₂ p q i j .R a b = R-sq a b i j
  where
    R-sq : ∀ a b
      → ap (λ z → R z a b) p ≡ ap (λ z → R z a b) q
    R-sq a b = Type-path-is-prop
      (prop k₁ a b) (prop k₂ a b)
      (ap (λ z → R z a b) p) (ap (λ z → R z a b) q)
K-is-set k₁ k₂ p q i j .strict =
  is-prop→SquareP
    (λ i j → strict-type-is-prop
      (K-is-set k₁ k₂ p q i j .R))
    (ap strict p)
    (λ _ → strict k₁)
    (ap strict q)
    (λ _ → strict k₂)
    i j
K-is-set k₁ k₂ p q i j .closed =
  is-prop→SquareP
    (λ i j → closed-type-is-prop
      (K-is-set k₁ k₂ p q i j .R)
      (λ a b → embedding→is-prop
        (K-is-set k₁ k₂ p q i j .strict .snd)
        Irr-is-prop))
    (ap closed p)
    (λ _ → closed k₁)
    (ap closed q)
    (λ _ → closed k₂)
    i j

```

## Face maps

The face map `∂-K i` restricts a relation from `Fin (S (S n))` to
`Fin (S n)` by precomposing with the coface injection `σ i`. Since
sigma is a strictly monotone injection, it preserves and reflects the
ordering, so strictness and interval-closure transfer.

```agda

∂-K : ∀ {u n} → Fin (S (S n)) → K u (S n) → K u n
∂-K i k .R a b = R k (σ i .map a) (σ i .map b)
∂-K i k .strict = strict k ∙↪ σ-reflects-<-emb i
∂-K i k .closed ab bc rac = closed k
  (σ-preserves-< i ab) (σ-preserves-< i bc) rac

```
