```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Lens.Covariant {u v} (R : Rx u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Path
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

module _ {w z} (B : Ob → Rx w z) where
  private module B x = Rx (B x)

  -- Pushforward along an edge
  Push : Type (u ⊔ v ⊔ w)
  Push = ∀ {x y} → x ~> y → B.₀ x → B.₀ y

  -- Oplax unitor: pushforward along ρ points back to original
  OplaxUnitor : Push → Type (u ⊔ w ⊔ z)
  OplaxUnitor P = ∀ {x} (u : B.₀ x) → B.₁ x (P (ρ x) u) u

  -- Universal pushforwards: fans at pushed vertices are props
  HasUniversalPush : Push → Type (u ⊔ v ⊔ w ⊔ z)
  HasUniversalPush P = ∀ {x y} (p : x ~> y) (u : B.₀ x)
                     → is-prop (Σ v ∶ B.₀ y , B.₁ y (P p u) v)

  -- Display of an oplax covariant lens
  module display (P : Push) (ε : OplaxUnitor P) where

    disp-vtx : Vtx w
    disp-vtx x = B.₀ x

    disp-edge : Edge z disp-vtx
    disp-edge {y = y} p u v = B.₁ y (P p u) v

    disp-drefl : DRefl disp-edge
    disp-drefl u = ε

    disp : DRx w z
    disp .DRx.vtx = disp-vtx
    disp .DRx.edge = disp-edge
    disp .DRx.drefl = disp-drefl

-- Bundled oplax covariant lens
record CovLens w z : Type (u ⊔ v ⊔ w ₊ ⊔ z ₊) where
  field
    family : Ob → Rx w z
  private module B x = Rx (family x)
  field
    push : ∀ {x y} → x ~> y → B.₀ x → B.₀ y
    oplax-unitor : ∀ {x} (u : B.₀ x) → B.₁ x (push (ρ x) u) u
