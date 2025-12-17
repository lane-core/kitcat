```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Component {u v} (R : Rx u v) where

open import Lib.Core.Prim
open import Lib.Path
open import Lib.Core.Type
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Component reflexive graph at a vertex x
-- Edges are displayed edges over ρ x
comp : ∀ {w z} (V : Vtx w) (E : Edge z V) (dr : DRefl E) (x : Ob) → Rx w z
comp V E dr x .Rx.₀ = V x
comp V E dr x .Rx.₁ u v = E (ρ x) u v
comp V E dr x .Rx.ρ u = dr u

-- Component fan matches displayed fan restricted to ρ
comp-fan : ∀ {w z} {V : Vtx w} {E : Edge z V} {dr : DRefl E} {x : Ob} (u : V x)
         → rx.fan (comp V E dr x) u ＝ (Σ v ∶ V x , E (ρ x) u v)
comp-fan u = refl
