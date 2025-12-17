```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Total {u v} (R : Rx u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Total reflexive graph from displayed structure
tot : ∀ {w z} (V : Vtx w) (E : Edge z V) (dr : DRefl E) → Rx (u ⊔ w) (v ⊔ z)
tot V E dr .Rx.₀ = Σ x ∶ Ob , V x
tot V E dr .Rx.₁ (x , u) (y , v) = Σ p ∶ (x ~> y) , E p u v
tot V E dr .Rx.ρ (x , u) = ρ x , dr x u

-- Total from bundled displayed
tot-DRx : ∀ {w z} → DRx w z → Rx (u ⊔ w) (v ⊔ z)
tot-DRx D = tot (DRx.vtx D) (DRx.edge D) (DRx.drefl D)

-- syntax tot V E dr = R ⦈ V , E , dr ⦊
