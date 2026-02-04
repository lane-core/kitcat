Displayed reflexive graphs over a base reflexive graph.

A `Disp-rx-graph` over a reflexive graph `R` consists of a family of types over
vertices, a family of edge types displayed over edges, and a displayed
reflexivity structure preserving the base reflexivity.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Core.Graph.Reflexive.Base
module Core.Graph.Reflexive.Displayed {u v} (R : Rx-graph u v) where

open import Core.Type
open import Core.Base
open import Core.Graph.Displayed (Rx-graph.graph R)

private module R = rx-graph R
open R renaming (₀ to Ob; ₁ to infix 4 _~>_) hiding (rx)

record Disp-rx-graph w z : Type (u ⊔ v ⊔ w ₊ ⊔ z ₊) where
  field
    disp : Disp-graph w z
    rx   : ∀ x (u : Disp-graph.Ob disp x) → Disp-graph.₂ disp (R.rx x) u u

  open Disp-graph disp public

module disp-rx-graph {w z} (D : Disp-rx-graph w z) where
  private module D = Disp-rx-graph D

  disp = D.disp
  rx   = D.rx

  open disp-graph disp public

```
