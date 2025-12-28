```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Graph.Base where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Core.Cast

record Graph u v : Type₊ (u ⊔ v) where
  constructor Gph
  field
    ₀ : Type u
    ₁ : ₀ → ₀ → Type v

  op : Graph u v
  op .₀ = ₀
  op .₁ x y = ₁ y x
{-# INLINE Gph #-}

record Graphical {u} (A : Type u) : Typeω where
  field
    {v e} : Level
    ∣_∣ : A → Type v
    _[_~>_] : ∀ x → ∣ x ∣ → ∣ x ∣ → Type e

  underlying-graph : A → Graph v e
  underlying-graph a .Graph.₀ = ∣ a ∣
  underlying-graph a .Graph.₁ = a [_~>_]
  {-# INLINE underlying-graph #-}
  {-# INLINE ∣_∣ #-}
  {-# INLINE _[_~>_] #-}

open Graphical ⦃ ... ⦄ using (∣_∣; _[_~>_]) public

instance
  Graphical-Graph : ∀ {u v} → Graphical (Graph u v)
  Graphical-Graph {u} .Graphical.v = u
  Graphical-Graph {v} .Graphical.e = v
  Graphical.∣ Graphical-Graph ∣ = Graph.₀
  Graphical-Graph .Graphical._[_~>_] = Graph.₁
  {-# INLINE Graphical-Graph #-}

module _ {u} {C : Type u} ⦃ G : Graphical C ⦄ where
  private module M = Graphical G
  private module G (c : C) = Graph (M.underlying-graph c)

  edge-syntax : (c : C) → G.₀ c → G.₀ c → Type (Graphical.e G)
  edge-syntax = G.₁
  syntax edge-syntax C x y = x ~> y ∶ C

  ob : (c : C) → Type (Graphical.v G)
  ob = G.₀

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




-- module _ {u v} {C : Type u} {D : Type v} ⦃ G : Graphical C ⦄ ⦃ F : Graphical D ⦄ where
--   private
--     module M = Graphical G
--     module N = Graphical F
--     module G c = Graph (M.underlying-graph c)
--     module F d = Graph (N.underlying-graph d)

--   gfunc : ∀ {a b} c d (P : Graph M.v M.e → Type a) (Q : Graph N.v N.e → Type b)
--         → (P (M.underlying-graph c) → Q (N.underlying-graph d))
--         → P (M.underlying-graph c) → Q (N.underlying-graph d)
--   gfunc c d P Q = λ f → f
