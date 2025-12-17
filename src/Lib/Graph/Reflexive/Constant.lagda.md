```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Constant {u v} (R : Rx u v) where

open import Lib.Core.Prim hiding (lift)
open import Lib.Path
open import Lib.Core.Type
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Constant displayed: R* S
-- Displayed vertices and edges don't depend on base edge
module _ {w z} (S : Rx w z) where
  private module S = Rx S

  const-vtx : Vtx w
  const-vtx _ = S.₀

  const-edge : Edge z const-vtx
  const-edge _ u v = S.₁ u v

  const-drefl : DRefl const-edge
  const-drefl _ x = S.ρ x

  const-disp : DRx w z
  const-disp .DRx.vtx = const-vtx
  const-disp .DRx.edge = const-edge
  const-disp .DRx.drefl x = const-drefl x

-- Notation: pullback along terminal map
_*_ : ∀ {w z} → Rx w z → DRx w z
_*_ s = const-disp s
