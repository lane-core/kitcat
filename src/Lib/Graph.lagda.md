```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Graph where

open import Lib.Type
open import Lib.Builtin
open import Lib.Cubical.Base
open import Lib.Underlying

record Graph u v : Type₊ (u ⊔ v) where
  constructor gph
  field
    ₀ : Type u
    ₁ : ₀ → ₀ → Type v
{-# INLINE gph #-}

instance
  Underlying-Graph : ∀ {u v} → Underlying (Graph u v)
  Underlying-Graph {u} .Underlying.ℓ-underlying = u
  Underlying-Graph .Underlying.⌞_⌟ = Graph.₀

-- _~>_ : ∀ {u v} ⦃ G : Graph u v ⦄ → ⌞ G ⌟ → ⌞ G ⌟ → Type v
-- _~>_ ⦃ G ⦄ = Graph.₁ G
-- infix 4 _~>_

is-reflexive-graph : ∀ {u} → Graph u u → Type u
is-reflexive-graph R = (x : R.₀) → R.₁ x x where module R = Graph R

Reflexive-graph : (u : Level) → Type₊ u
Reflexive-graph u = Σ R ∶ Graph u u , is-reflexive-graph R

module Reflexive-graph {u} (R : Reflexive-graph u) where
  ₀ : Type u
  ₀ = Graph.₀ (R .fst)

  ₁ : ₀ → ₀ → Type u
  ₁ = Graph.₁ (R .fst)

  rx : ∀ x → ₁ x x
  rx = R .snd

-- record Homotopical-graph u v  : Type₊ (u ⊔ v) where
--   constructor hgph
--   field
--     ₀ : Type u
--     ₁ : ₀ → ₀ → Type v
--     ₂ : ∀ {x y} → ₁ x y → ₁ x y → Type v
--     hrx : ∀ {x y} (h : ₁ x y) → ₂ h h

--   instance
--     htpy→#graph : Graph u v
--     htpy→#graph .Graph.₀ = ₀
--     htpy→#graph .Graph.₁ = ₁

--     htpy→#rx-graph : {x y : ₀} → Reflexive-graph v
--     htpy→#rx-graph {x} {y} .Reflexive-graph.₀ = x ~> y
--     htpy→#rx-graph .Reflexive-graph.₁ = ₂
--     htpy→#rx-graph .Reflexive-graph.rx = hrx

-- {-# INLINE hgph #-}


-- instance
--   Underlying-Htpy-graph : ∀ {u v} → Underlying (Homotopical-graph u v)
--   Underlying-Htpy-graph {u} .Underlying.ℓ-underlying = u
--   Underlying-Htpy-graph .Underlying.⌞_⌟ = Homotopical-graph.₀

--   Quiver-Htpy-graph : ∀ {u v} ⦃ G : Homotopical-graph u v ⦄ → Quiver v (Homotopical-graph.₀ G)
--   Quiver-Htpy-graph ⦃ G ⦄ .Quiver._~>_ = Homotopical-graph.₁ G

--   Congruence-Htpy-graph : ∀ {u v} ⦃ G : Homotopical-graph u v ⦄ {x y} → Congruence (Homotopical-graph.₁ G x y)
--   Congruence-Htpy-graph ⦃ G ⦄ .Congruence._≈_ = Homotopical-graph.₂ G

-- Gph-functor : ∀ {u v} (G : A → )
