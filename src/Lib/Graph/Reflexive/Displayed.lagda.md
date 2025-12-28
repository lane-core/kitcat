```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

import Lib.Graph.Displayed
import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Displayed {u v} (R : Lib.Graph.Reflexive.Base.Rx u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open Lib.Graph.Reflexive.Base.Rx R renaming (₀ to V; ₁ to infix 4 _~>_)
open import Lib.Core.Base

private module D = Lib.Graph.Displayed gph

-- Bundled displayed reflexive graph
record Disp-rx w z : Type (u ⊔ v ⊔ w ₊ ⊔ z ₊) where
  field
    Ob : V → Type w
    ₂ : ∀ {x y} → x ~> y → Ob x → Ob y → Type z
    drx : ∀ x (u : Ob x) → ₂ (rx x) u u

  to-display : D.Display w z
  to-display .D.Display.Ob = Ob
  to-display .D.Display.₂ = ₂

module display {w z} (D : Disp-rx w z) = Lib.Graph.Displayed.display gph (Disp-rx.to-display D)
