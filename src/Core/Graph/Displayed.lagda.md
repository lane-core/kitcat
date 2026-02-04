Displayed graphs over a base graph.

A `Disp-graph` over a graph `R` consists of a family of types over vertices and
a family of edge types displayed over edges. This gives the foundation for
displayed categories and dependent type-theoretic constructions over graphs.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Core.Graph.Base
module Core.Graph.Displayed {u v} (R : Graph u v) where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open Graph R renaming (₀ to V; ₁ to infix 4 _~>_)

record Disp-graph w z : Type (u ⊔ v ⊔ w ₊ ⊔ z ₊) where
  field
    Ob : V → Type w
    ₂  : ∀ {x y} → x ~> y → Ob x → Ob y → Type z

module disp-graph {w z} (D : Disp-graph w z) where
  open Disp-graph D renaming (₂ to E)

  dep-fan : ∀ {x} → Ob x → Type (u ⊔ v ⊔ w ⊔ z)
  dep-fan {x} u = Σ y ∶ V , Σ p ∶ (x ~> y) , Σ v ∶ Ob y , E p u v

  dep-cofan : ∀ {y} → Ob y → Type (u ⊔ v ⊔ w ⊔ z)
  dep-cofan {y} v = Σ x ∶ V , Σ p ∶ (x ~> y) , Σ u ∶ Ob x , E p u v


  -- Covariant fibration: unique lifts forward
  is-cov-fib : Type (u ⊔ v ⊔ w ⊔ z)
  is-cov-fib = ∀ {x y} (p : x ~> y) (u : Ob x) → is-contr (Σ v ∶ Ob y , E p u v)

  -- Contravariant fibration: unique lifts backward
  is-ctrv-fib : Type (u ⊔ v ⊔ w ⊔ z)
  is-ctrv-fib = ∀ {x y} (p : x ~> y) (v : Ob y) → is-contr (Σ u ∶ Ob x , E p u v)


  -- Pushforward (from covariant fibration)
  module is-cov-fib (fib : is-cov-fib) where
    push : ∀ {x y} → x ~> y → Ob x → Ob y
    push p u = fib p u .center .fst

    lift : ∀ {x y} (p : x ~> y) (u : Ob x) → E p u (push p u)
    lift p u = fib p u .center .snd

    lift-unique
      : ∀ {x y} (p : x ~> y) (u : Ob x) (v : Ob y) (e : E p u v)
      → (push p u , lift p u) ≡ (v , e)
    lift-unique p u v e = fib p u .paths (v , e)

  -- Pullback (from contravariant fibration)
  module ctrv-fib (fib : is-ctrv-fib) where
    pull : ∀ {x y} → x ~> y → Ob y → Ob x
    pull p v = fib p v .center .fst

    colift : ∀ {x y} (p : x ~> y) (v : Ob y) → E p (pull p v) v
    colift p v = fib p v .center .snd

    colift-unique
      : ∀ {x y} (p : x ~> y) (v : Ob y) (u : Ob x) (e : E p u v)
      → (pull p v , colift p v) ≡ (u , e)
    colift-unique p v u e = fib p v .paths (u , e)

```
