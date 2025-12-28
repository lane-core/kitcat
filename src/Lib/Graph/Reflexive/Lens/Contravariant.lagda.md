```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

import Lib.Graph.Reflexive.Base
import Lib.Graph.Reflexive.Displayed

module Lib.Graph.Reflexive.Lens.Contravariant {u v w z}
  (R : Lib.Graph.Reflexive.Base.Rx u v)
  (let module D = Lib.Graph.Reflexive.Displayed R)
  (D : D.Disp-rx w z) where

open Lib.Graph.Reflexive.Base
private module G = Lib.Graph.Reflexive.Displayed.Disp-rx D

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

module ctrv where
  -- pullback along an edge
  pull : Type (u ⊔ v ⊔ w)
  pull = ∀ {x y} → x ~> y → G.vtx y → G.vtx x

  -- Lax unitor: original points to pullback along rx
  lax-unitor : pull → Type (u ⊔ w ⊔ z)
  lax-unitor P = ∀ {x} (u : G.vtx x) → G.₂ (rx x) u (P (rx x) u) -- x u (P (rx x) u)

  universal-pull : pull → Type (u ⊔ v ⊔ w ⊔ z)
  universal-pull P = ∀ {x y} (p : x ~> y) (v : G.vtx y)
                     → is-prop (Σ u ∶ G.vtx x , G.₂ (rx x) u (P p v)) -- x u (P p v))

  -- lax contravariant lens
  record lens : Type (u ⊔ v ⊔ w ⊔ z) where
    field
      has-pull : ∀ {x y} → x ~> y → G.vtx y → G.vtx x
      has-lax-unitor : lax-unitor has-pull

    disp : Lib.Graph.Reflexive.Displayed.Disp-rx R w z
    disp .D.Disp-rx.vtx x = G.vtx x
    disp .D.Disp-rx.₂ {x = x} p u v = G.₂ (rx x) u (has-pull p v)
    disp .D.Disp-rx.drefl x u = has-lax-unitor u
