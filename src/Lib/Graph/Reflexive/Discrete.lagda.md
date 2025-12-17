```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Graph.Reflexive.Discrete where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Path
open import Lib.Graph.Reflexive.Base

-- Discrete reflexive graph: edges are identity types
disc : ∀ {ℓ} → Type ℓ → Rx ℓ ℓ
disc A .Rx.₀ = A
disc A .Rx.₁ x y = x ≡ y
disc A .Rx.ρ x = refl

-- Discrete is always univalent
disc-is-univalent : ∀ {ℓ} (A : Type ℓ) → rx.is-univalent (disc A)
disc-is-univalent A x (y , p) (z , q) = Σ-path (p ∙ sym q) {!!}

-- Notation
△ : ∀ {ℓ} → Type ℓ → Rx ℓ ℓ
△ = disc

-- Codiscrete reflexive graph: edges are trivial
codisc : ∀ {ℓ} → Type ℓ → Rx ℓ 0ℓ
codisc A .Rx.₀ = A
codisc A .Rx.₁ _ _ = ⊤
codisc A .Rx.ρ _ = tt

-- Codiscrete is univalent when A is a proposition
codisc-is-univalent : ∀ {ℓ} (A : Type ℓ) → is-prop A → rx.is-univalent (codisc A)
codisc-is-univalent A A-prop x (y , _) (z , _) =
  Σ-path (A-prop y z) refl

-- Notation
▽ : ∀ {ℓ} → Type ℓ → Rx ℓ 0ℓ
▽ = codisc
