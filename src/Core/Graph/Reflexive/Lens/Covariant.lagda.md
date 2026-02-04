Covariant lenses on displayed reflexive graphs.

A covariant lens provides a way to push displayed vertices forward along
edges, with an oplax unitor witnessing coherence with reflexivity.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

import Core.Graph.Reflexive.Base
import Core.Graph.Reflexive.Displayed

module Core.Graph.Reflexive.Lens.Covariant {u v w z}
  (R : Core.Graph.Reflexive.Base.Rx-graph u v)
  (let module RD = Core.Graph.Reflexive.Displayed R)
  (E : RD.Disp-rx-graph w z) where

open Core.Graph.Reflexive.Base
open import Core.Graph.Base using (Graph)
open import Core.Graph.Displayed (Rx-graph.graph R) using (Disp-graph)

open import Core.Type
open import Core.Base

private
  module R = rx-graph R
  module G = RD.Disp-rx-graph E

open R using (rx; gph)
open Graph gph renaming (₀ to V; ₁ to infix 4 _~>_)

module cov where
  -- Pushforward along an edge
  push : Type (u ⊔ v ⊔ w)
  push = ∀ {x y} → x ~> y → G.Ob x → G.Ob y

  -- Oplax unitor: pushforward along rx points to original
  oplax-unitor : push → Type (u ⊔ w ⊔ z)
  oplax-unitor P = ∀ {x} (u : G.Ob x) → G.₂ (rx x) (P (rx x) u) u

  -- Lax covariant lens
  record lens : Type (u ⊔ v ⊔ w ⊔ z) where
    field
      has-push : ∀ {x y} → x ~> y → G.Ob x → G.Ob y
      has-oplax-unitor : oplax-unitor has-push

    disp : RD.Disp-rx-graph w z
    disp .RD.Disp-rx-graph.disp .Disp-graph.Ob x = G.Ob x
    disp .RD.Disp-rx-graph.disp .Disp-graph.₂ {y = y} p u = G.₂ (rx y) (has-push p u)
    disp .RD.Disp-rx-graph.rx x u = has-oplax-unitor u

```
