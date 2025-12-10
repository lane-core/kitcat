```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Graph.Virtual where

open import Lib.Type
open import Lib.Builtin
open import Lib.Path
open import Lib.Graph
open import Lib.Underlying

record virtual-equipment {u v} (G : Graph u v) : Type (u ⊔ v ₊) where
  private
    module G = Graph G
    _~>_ = Graph.₁ G

  field
    Htpy : ∀ {x y} → x ~> y → x ~> y → Type v
    concat : ∀ {x y z} → x ~> y → y ~> z → x ~> z

  private
    _≈_ = Htpy
    _∙_ = concat

  field
    heqv : ∀ {x y} {f : x ~> y} → f ≈ f
    hsym : {x y : G.₀} {f g : x ~> y} → f ≈ g → g ≈ f
    vconcat : {x y : G.₀} {f g h : x ~> y} → f ≈ g → g ≈ h → f ≈ h
    hconcat : {x y z : G.₀} {e1 d1 : x ~> y} {e2 d2 : y ~> z}
         → e1 ≈ d1 → e2 ≈ d2 → (e1 ∙ e2) ≈ (d1 ∙ d2)

  -- we can show that the notion of 2-cell composition corresponds
  -- to path groupoid composition. hence n+1 cells always themselves comprise
  -- a virtual graph
  hseq2 : {x y : G.₀} {f g h : x ~> y} {e1 d1 : f ≈ g} {e2 d2 : g ≈ h}
         → e1 ＝ d1 → e2 ＝ d2 → (vconcat e1 e2) ＝ (vconcat d1 d2)
  hseq2 {e1} {e2} H K = subst2 (λ s r → vconcat e1 e2 ＝ vconcat s r) H K refl

Virtual-graph : (u v : Level) → Type₊ (u ⊔ v)
Virtual-graph u v = Σ G ∶ Graph u v , virtual-equipment G
