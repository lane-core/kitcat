Reflexive graphs: graphs with a reflexivity structure.

This module is based on Sterling's Reflexive Graph Lenses paper.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Graph.Reflexive.Base where

open import Core.Type
open import Core.Equiv
open import Core.Data.Sigma
open import Core.Kan
open import Core.HLevel
open import Core.Base
open import Core.Transport
open import Core.Trait.Cast
open import Core.Graph.Base

record Rx-graph u v : Type₊ (u ⊔ v) where
  field
    graph : Graph u v
    rx    : graph.reflexive graph

instance
  Graphical-Rx-graph : ∀ {u v} → Graphical (Rx-graph u v)
  Graphical-Rx-graph {u} .Graphical.v = u
  Graphical-Rx-graph {v = v} .Graphical.e = v
  Graphical.∣ Graphical-Rx-graph ∣ R = Graph.₀ (Rx-graph.graph R)
  Graphical-Rx-graph .Graphical._[_~>_] R = Graph.₁ (Rx-graph.graph R)

module rx-graph {u v} (R : Rx-graph u v) where
  private module R = Rx-graph R

  gph = R.graph
  rx  = R.rx

  open Graph gph renaming (₀ to Ob; ₁ to infix 4 _≈_) hiding (op)
  ₀ = Graph.₀ gph
  ₁ = Graph.₁ gph
  open graph gph public

  -- Fan centered at reflexivity
  fan-center : ∀ x → fan x
  fan-center x = x , rx x

  -- Cofan centered at reflexivity
  cofan-center : ∀ x → cofan x
  cofan-center x = x , rx x

  to-edge : ∀ {x y} → x ≡ y → x ≈ y
  to-edge {x} p = transport (λ i → x ≈ p i) (rx x)

  op : Rx-graph u v
  op .Rx-graph.graph .Graph.₀ = Ob
  op .Rx-graph.graph .Graph.₁ x y = y ≈ x
  op .Rx-graph.rx = rx

  module is-univalent (univ : is-univalent) where
    -- Fan contractibility from univalence
    fan-contr : ∀ x → is-contr (fan x)
    fan-contr x = prop-inhabited→is-contr (univ x) (x , rx x)

    -- Edge-to-identity (inverse of to-edge)
    to-id : ∀ {x y} → x ≈ y → x ≡ y
    to-id {x} {y} p = ap fst (univ x (x , rx x) (y , p))

    -- Concatenation of edges
    edge-concat : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
    edge-concat p q = to-edge (to-id p ∙ to-id q)

    -- Inverse of edge
    inv : ∀ {x y} → x ≈ y → y ≈ x
    inv p = to-edge (sym (to-id p))

```
