```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Displayed {u v} (R : Rx u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)
open import Lib.Path
open import Lib.Underlying

-- Displayed vertices over base
Vtx : ∀ w → Type (u ⊔ w ₊)
Vtx w = Ob → Type w

-- Displayed edges over a base edge
Edge : ∀ {w} z → Vtx w → Type (u ⊔ v ⊔ w ⊔ z ₊)
Edge z V = ∀ {x y} → x ~> y → V x → V y → Type z

-- Displayed reflexivity
DRefl : ∀ {w z} {V : Vtx w} → Edge z V → Type (u ⊔ w ⊔ z)
DRefl {V = V} E = ∀ x (u : V x) → E (ρ x) u u

-- Displayed fan at a vertex
DFan : ∀ {w z} {V : Vtx w} → Edge z V → ∀ {x} → V x → Type (u ⊔ v ⊔ w ⊔ z)
DFan {V = V} E {x} u = Σ y ∶ Ob , Σ p ∶ (x ~> y) , Σ v ∶ V y , E p u v

-- Displayed co-fan at a vertex
DCoFan : ∀ {w z} {V : Vtx w} → Edge z V → ∀ {y} → V y → Type (u ⊔ v ⊔ w ⊔ z)
DCoFan {V = V} E {y} v = Σ x ∶ Ob , Σ p ∶ (x ~> y) , Σ u ∶ V x , E p u v

-- Displayed univalence: component reflexive graphs are univalent
is-disp-univalent : ∀ {w z} {V : Vtx w} → Edge z V → Type (u ⊔ w ⊔ z)
is-disp-univalent {V = V} E = ∀ {x} (u : V x) → is-prop (Σ v ∶ V x , E (ρ x) u v)

-- Bundled displayed reflexive graph
record DRx w z : Type (u ⊔ v ⊔ w ₊ ⊔ z ₊) where
  field
    vtx : Vtx w
    edge : Edge z vtx
    drefl : DRefl edge
