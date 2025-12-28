This set of modules is based on Sterling's Reflexive Graph Lenses paper

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Graph.Reflexive.Base where

open import Lib.Core.Prim
open import Lib.Core.Equiv
open import Lib.Core.Type
open import Lib.Core.Kan
open import Lib.Core.HLevel
open import Lib.Core.Base
open import Lib.Core.Transport
open import Lib.Core.Cast
open import Lib.Graph.Base

Rx : ∀ u v → Type₊ (u ⊔ v)
Rx u v = Σ G ∶ Graph u v , graph.reflexive G

instance
  Graphical-Rx : ∀ {u v} → Graphical (Rx u v)
  Graphical-Rx {u} .Graphical.v = u
  Graphical-Rx {v} .Graphical.e = v
  Graphical.∣ Graphical-Rx ∣ = Graph.₀ ∘ fst
  Graphical-Rx .Graphical._[_~>_] = Graph.₁ ∘ fst

module Rx {u v} (R : Rx u v) where
  open Σ R public renaming (fst to gph; snd to rx)
  open Graph gph renaming (₀ to Ob; ₁ to infix 4 _≈_) hiding (op)
  ₀ = Graph.₀ (fst R)
  ₁ = Graph.₁ (fst R)
  open graph gph public

  -- Fan centered at reflexivity
  fan-center : ∀ x → fan x
  fan-center x = x , rx x

  -- Cofan centered at reflexivity
  cofan-center : ∀ x → cofan x
  cofan-center x = x , rx x

  to-edge : ∀ {x y} → x ≡ y → x ≈ y
  to-edge {x} p = transport (λ i → x ≈ p i) (rx x)

  op : Rx u v
  op .fst .Graph.₀ = Ob
  op .fst .Graph.₁ x y = y ≈ x
  op .snd = rx

  module is-univalent (univ : is-univalent) where
    -- Fan contractibility from univalence
    fan-contr : ∀ x → is-contr (fan x)
    fan-contr x = prop-inhabited→is-contr (univ x) (x , rx x)

    -- Edge-to-identity (inverse of to-edge)
    to-id : ∀ {x y} → x ≈ y → x ≡ y
    to-id {x} {y} p = ap fst (univ x (x , rx x) (y , p))

    -- Concatenation of edges
    concat : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
    concat p q = to-edge (to-id p ∙ to-id q)

    -- Inverse of edge
    inv : ∀ {x y} → x ≈ y → y ≈ x
    inv p = to-edge (sym (to-id p))

    -- Groupoid laws (all trivial from path structure)

    -- ∙ₑ-unitl : ∀ {x y} (p : x ≈ y) → rx x ∙ₑ p ≡ p
    -- ∙ₑ-unitl {x} p = ap to-edge (∙-unitl (to-id p)) ∙ {!!}

    -- ∙ₑ-unitr : ∀ {x y} (p : x ≈ y) → p ∙ₑ rx y ≡ p
    -- ∙ₑ-unitr {y = y} p = ap to-edge (∙-unitr (to-id p)) ∙ {!!}

    -- ∙ₑ-assoc : ∀ {w x y z} (p : w ≈ x) (q : x ≈ y) (r : y ≈ z)
    --          → (p ∙ₑ q) ∙ₑ r ≡ p ∙ₑ (q ∙ₑ r)
    -- ∙ₑ-assoc p q r = ap to-edge (∙-assoc (to-id p) (to-id q) (to-id r)) ∙ {!!}

    -- ∙ₑ-invl : ∀ {x y} (p : x ≈ y) → p ⁻¹ₑ ∙ₑ p ≡ rx y
    -- ∙ₑ-invl p = {!!}

    -- ∙ₑ-invr : ∀ {x y} (p : x ≈ y) → p ∙ₑ p ⁻¹ₑ ≡ rx x
    -- ∙ₑ-invr p = {!!}

    -- Transport along edge
    -- substₑ : ∀ {ℓ} {x y} (P : Ob → Type ℓ) → x ≈ y → P x → P y
    -- substₑ P p = subst P (to-id p)
