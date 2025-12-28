```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

import Lib.Graph.Reflexive.Base
import Lib.Graph.Reflexive.Displayed

module Lib.Graph.Reflexive.Lens.Covariant {u v w z}
  (R : Lib.Graph.Reflexive.Base.Rx u v)
  (let module D = Lib.Graph.Reflexive.Displayed R)
  (D : D.Disp-rx w z) where

open Lib.Graph.Reflexive.Base
private module G = Lib.Graph.Reflexive.Displayed.Disp-rx D

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

module cov where
  -- pushback along an edge
  push : Type (u ⊔ v ⊔ w)
  push = ∀ {x y} → x ~> y → G.vtx x → G.vtx y

  -- Lax unitor: original points to pushback along rx
  oplax-unitor : push → Type (u ⊔ w ⊔ z)
  oplax-unitor P = ∀ {x} (u : G.vtx x) → G.₂ (rx x) (P (rx x) u) u

  universal-push : push → Type (u ⊔ v ⊔ w ⊔ z)
  universal-push P = ∀ {x y} (p : x ~> y) (u : G.vtx x)
                   → is-prop (Σ v ∶ G.vtx y , G.₂ (rx y) (P p u) v)

  -- lax contravariant lens
  record lens : Type (u ⊔ v ⊔ w ⊔ z) where
    field
      has-push : ∀ {x y} → x ~> y → G.vtx x → G.vtx y
      has-oplax-unitor : oplax-unitor has-push

    disp : Lib.Graph.Reflexive.Displayed.Disp-rx R w z
    disp .D.Disp-rx.vtx x = G.vtx x
    disp .D.Disp-rx.₂ {y = y} p u = G.₂ (rx y) (has-push p u)
    disp .D.Disp-rx.drefl x u = has-oplax-unitor u
