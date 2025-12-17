```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Tensor {u v} (R : Rx u v)where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Path

open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Tensor: scale vertices by a type A
-- Edges ignore the A component
_·_ : ∀ {ℓ} → Type ℓ → Rx (ℓ ⊔ u) v
(_·_) A .Rx.₀ = A × Ob
(_·_) A .Rx.₁ (a , x) (b , y) = x ~> y
(_·_) A .Rx.ρ (a , x) = ρ x
infixr 40 _·_

-- Tensor preserves univalence when A is contractible
-- ·-preserves-univalent : ∀ {ℓ} (A : Type ℓ) → is-contr A
--                       → rx.is-univalent R → rx.is-univalent (A · )
-- ·-preserves-univalent A A-contr R-univ (a , x) = {!!}
