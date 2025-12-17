```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Lens.Contravariant {u v} (R : Rx u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Path
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

module _ {w z} (B : Ob → Rx w z) where
  private module B x = Rx (B x)

  -- Pullback along an edge
  Pull : Type (u ⊔ v ⊔ w)
  Pull = ∀ {x y} → x ~> y → B.₀ y → B.₀ x

  -- Lax unitor: original points to pullback along ρ
  LaxUnitor : Pull → Type (u ⊔ w ⊔ z)
  LaxUnitor P = ∀ {x} (u : B.₀ x) → B.₁ x u (P (ρ x) u)

  -- Universal pullbacks: co-fans at pulled vertices are props
  HasUniversalPull : Pull → Type (u ⊔ v ⊔ w ⊔ z)
  HasUniversalPull P = ∀ {x y} (p : x ~> y) (v : B.₀ y)
                     → is-prop (Σ u ∶ B.₀ x , B.₁ x u (P p v))

  -- Display of a lax contravariant lens
  module display (P : Pull) (η : LaxUnitor P) where

    disp-vtx : Vtx w
    disp-vtx x = B.₀ x

    disp-edge : Edge z disp-vtx
    disp-edge {x = x} p u v = B.₁ x u (P p v)

    disp-drefl : DRefl disp-edge
    disp-drefl u = η

    disp : DRx w z
    disp .DRx.vtx = disp-vtx
    disp .DRx.edge = disp-edge
    disp .DRx.drefl = disp-drefl

-- Bundled lax contravariant lens
record CtrvLens w z : Type (u ⊔ v ⊔ w ₊ ⊔ z ₊) where
  field
    family : Ob → Rx w z
  private module B x = Rx (family x)
  field
    pull : ∀ {x y} → x ~> y → B.₀ y → B.₀ x
    lax-unitor : ∀ {x} (u : B.₀ x) → B.₁ x u (pull (ρ x) u)
