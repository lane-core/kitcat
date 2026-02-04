Directed graphs.

A `Graph` consists of a type of vertices and a family of edge types between
them. This module defines the `Graph` record and its `Graphical` instance.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Graph.Base where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Trait.Graphical public

record Graph u v : Type₊ (u ⊔ v) where
  constructor Gph
  field
    ₀ : Type u
    ₁ : ₀ → ₀ → Type v

  op : Graph u v
  op .₀ = ₀
  op .₁ x y = ₁ y x
{-# INLINE Gph #-}

instance
  Graphical-Graph : ∀ {u v} → Graphical (Graph u v)
  Graphical-Graph {u} .Graphical.v = u
  Graphical-Graph {v = v} .Graphical.e = v
  Graphical-Graph .Graphical.∣_∣ = Graph.₀
  Graphical-Graph .Graphical._[_~>_] = Graph.₁
  {-# INLINE Graphical-Graph #-}

module graph {u v} (G : Graph u v) where
  private module G = Graph G; _~>_ = G.₁; infix 6 _~>_

  module displayed where
    vtx : ∀ w → Type (u ⊔ w ₊)
    vtx w = ∣ G ∣ → Type w

    edge : ∀ {w} z → vtx w → Type (u ⊔ v ⊔ w ⊔ z ₊)
    edge z V = ∀ {x y} → G.₁ x y → V x → V y → Type z

  reflexive = ∀ x → G.₁ x x
  involutive = ∀ {x y} → G.₁ x y → G.₁ y x
  transitive = ∀ {x y z} → G.₁ x y → G.₁ y z → G.₁ x z

  -- Fan (outward): edges out of a vertex
  fan : G.₀ → Type (u ⊔ v)
  fan x = Σ y ∶ G.₀ , x ~> y

  -- Cofan (inward): edges into a vertex
  cofan : G.₀ → Type (u ⊔ v)
  cofan y = Σ x ∶ G.₀ , x ~> y

  -- Univalence: fans are propositional
  is-univalent : Type (u ⊔ v)
  is-univalent = ∀ x → is-prop (fan x)

  -- Equivalent via cofans
  is-univalent-op : Type (u ⊔ v)
  is-univalent-op = ∀ y → is-prop (cofan y)

```
