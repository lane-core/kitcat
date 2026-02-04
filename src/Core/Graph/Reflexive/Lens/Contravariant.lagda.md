Contravariant lenses on displayed reflexive graphs.

A contravariant lens provides a way to pull displayed vertices backward along
edges, with a lax unitor witnessing coherence with reflexivity.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

import Core.Graph.Reflexive.Base
import Core.Graph.Reflexive.Displayed

module Core.Graph.Reflexive.Lens.Contravariant {u v w z}
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

module ctrv where
  -- Pullback along an edge
  pull : Type (u ⊔ v ⊔ w)
  pull = ∀ {x y} → x ~> y → G.Ob y → G.Ob x

  -- Lax unitor: original points to pullback along rx
  lax-unitor : pull → Type (u ⊔ w ⊔ z)
  lax-unitor P = ∀ {x} (u : G.Ob x) → G.₂ (rx x) u (P (rx x) u)

  -- Lax contravariant lens
  record lens : Type (u ⊔ v ⊔ w ⊔ z) where
    field
      has-pull : ∀ {x y} → x ~> y → G.Ob y → G.Ob x
      has-lax-unitor : lax-unitor has-pull

    disp : RD.Disp-rx-graph w z
    disp .RD.Disp-rx-graph.disp .Disp-graph.Ob x = G.Ob x
    disp .RD.Disp-rx-graph.disp .Disp-graph.₂ {x = x} p u v = G.₂ (rx x) u (has-pull p v)
    disp .RD.Disp-rx-graph.rx x u = has-lax-unitor u

```
