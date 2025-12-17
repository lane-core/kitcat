```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Comprehension {u v} (R : Rx u v) where

open import Lib.Core.Prim hiding (lift)
open import Lib.Path
open import Lib.Core.Type
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Comprehension: subgraph satisfying predicate P
-- Edges project down to base
compr : ∀ {ℓ} (P : Ob → Type ℓ) → Rx (u ⊔ ℓ) v
compr P .Rx.₀ = Σ x ∶ Ob , P x
compr P .Rx.₁ (x , _) (y , _) = x ~> y
compr P .Rx.ρ (x , _) = ρ x

-- Notation
syntax compr (λ x → P) = [ x ∣ P ]

-- Comprehension preserves univalence when P is propositional
-- compr-preserves-univalent : ∀ {ℓ} {P : Ob → Type ℓ}
--                           → (∀ x → is-prop (P x))
--                           → rx.is-univalent R
--                           → rx.is-univalent (compr P)
-- compr-preserves-univalent P-prop R-univ (x , px) f0 f1 i = {!!} , {!f0 .snd!}
