```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

import Lib.Graph.Reflexive.Base
import Lib.Graph.Reflexive.Displayed

module Lib.Graph.Reflexive.Lens.Midpoint {u v} (R : Lib.Graph.Reflexive.Base.Rx u v) where

open Lib.Graph.Reflexive.Base

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

module midpoint {w z} (B : ∀ {x y} → x ~> y → Rx w z) where
  private module B {x} {y} p = Rx (B {x} {y} p)

  left-injective : Type (u ⊔ v ⊔ w)
  left-injective = ∀ {x y} (p : x ~> y) → B.₀ (rx x) → B.₀ p

  right-injective : Type (u ⊔ v ⊔ w)
  right-injective = ∀ {x y} (p : x ~> y) → B.₀ (rx y) → B.₀ p

  mid-unitor : left-injective → right-injective → Type (u ⊔ w ⊔ z)
  mid-unitor L R = ∀ {x} (u : B.₀ (rx x)) → B.₁ (rx x) (L (rx x) u) (R (rx x) u)

  lax-unitor : right-injective → Type (u ⊔ w ⊔ z)
  lax-unitor R = ∀ {x} (u : B.₀ (rx x)) → B.₁ (rx x) u (R (rx x) u)

  record mid-lens : Type (u ⊔ v ⊔ w ⊔ z) where
    field
      linj : left-injective
      rinj : right-injective
      munitor : mid-unitor linj rinj
      rinj-lax-unitor : lax-unitor rinj
