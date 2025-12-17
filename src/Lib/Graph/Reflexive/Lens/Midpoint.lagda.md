```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Lens.Midpoint {u v} (R : Rx u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Path
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

module _ {w z} (B : ∀ {x y} → x ~> y → Rx w z) where
  private module B {x} {y} p = Rx (B {x} {y} p)

  -- Left injection: from source's ρ-component into edge component
  LInj : Type (u ⊔ v ⊔ w)
  LInj = ∀ {x y} (p : x ~> y) → B.₀ (ρ x) → B.₀ p

  -- Right injection: from target's ρ-component into edge component
  RInj : Type (u ⊔ v ⊔ w)
  RInj = ∀ {x y} (p : x ~> y) → B.₀ (ρ y) → B.₀ p

  -- Midpoint unitor: L and R connect at ρ
  MidUnitor : LInj → RInj → Type (u ⊔ w ⊔ z)
  MidUnitor L R = ∀ {x} (u : B.₀ (ρ x))
                → B.₁ (ρ x) (L (ρ x) u) (R (ρ x) u)

  -- Lax unitor for right injection
  RInjLaxUnitor : RInj → Type (u ⊔ w ⊔ z)
  RInjLaxUnitor R = ∀ {x} (u : B.₀ (ρ x)) → B.₁ (ρ x) u (R (ρ x) u)

  -- Display of a bivariant midpoint lens
  module display (L : LInj) (R : RInj) (μ : MidUnitor L R) where
    disp-vtx : Vtx w
    disp-vtx x = B.₀ (ρ x)

    disp-edge : Edge z disp-vtx
    disp-edge p u v = B.₁ p (L p u) (R p v)

    disp-drefl : DRefl disp-edge
    disp-drefl u = μ u

    disp : DRx w z
    disp .DRx.vtx = disp-vtx
    disp .DRx.edge = disp-edge
    disp .DRx.drefl = disp-drefl

-- Bundled bivariant midpoint lens
record MidLens w z : Type (u ⊔ v ⊔ w ₊ ⊔ z ₊) where
  field
    family : ∀ {x y} → x ~> y → Rx w z
  private module B {x} {y} p = Rx (family {x} {y} p)
  field
    linj : ∀ {x y} (p : x ~> y) → B.₀ (ρ x) → B.₀ p
    rinj : ∀ {x y} (p : x ~> y) → B.₀ (ρ y) → B.₀ p
    mid-unitor : ∀ {x} (u : B.₀ (ρ x)) → B.₁ (ρ x) (linj (ρ x) u) (rinj (ρ x) u)
    rinj-lax : ∀ {x} (u : B.₀ (ρ x)) → B.₁ (ρ x) u (rinj (ρ x) u)
