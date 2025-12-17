```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Pitchfork {u v} (R : Rx u v)where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Path

open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Pitchfork (exponential): functions into R with pointwise edges
_⦶_ : ∀ {ℓ} → Type ℓ → Rx (ℓ ⊔ u) (ℓ ⊔ v)
(_⦶_) A .Rx.₀ = A → Ob
(_⦶_) A .Rx.₁ f g = ∀ a → f a ~> g a
(_⦶_) A .Rx.ρ f a = ρ (f a)

-- -- Pitchfork preserves univalence (requires funext)
-- ⦶-preserves-univalent : ∀ {ℓ} (A : Type ℓ)
--                        → rx.is-univalent R → rx.is-univalent (A ⦶ )
-- ⦶-preserves-univalent A R-univ f = {!!}
