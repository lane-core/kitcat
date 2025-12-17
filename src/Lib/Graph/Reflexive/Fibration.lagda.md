```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Fibration {u v} (R : Rx u v) where

open import Lib.Core.Prim hiding (lift)
open import Lib.Path
open import Lib.Core.Type
open import Lib.Graph.Reflexive.Displayed R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

module _ {w z} {V : Vtx w} (E : Edge z V) where
  -- Covariant fibration: unique lifts forward
  is-cov-fib : Type (u ⊔ v ⊔ w ⊔ z)
  is-cov-fib = ∀ {x y} (p : x ~> y) (u : V x)
             → is-contr (Σ v ∶ V y , E p u v)

  -- Contravariant fibration: unique lifts backward
  is-ctrv-fib : Type (u ⊔ v ⊔ w ⊔ z)
  is-ctrv-fib = ∀ {x y} (p : x ~> y) (v : V y)
              → is-contr (Σ u ∶ V x , E p u v)

  -- Pushforward (from covariant fibration)
  module cov-fib (fib : is-cov-fib) where
    push : ∀ {x y} → x ~> y → V x → V y
    push p u = fib p u .center .fst

    lift : ∀ {x y} (p : x ~> y) (u : V x) → E p u (push p u)
    lift p u = fib p u .center .snd

    lift-unique : ∀ {x y} (p : x ~> y) (u : V x) (v : V y) (e : E p u v)
                → (push p u , lift p u) ＝ (v , e)
    lift-unique p u v e = fib p u .paths (v , e)

  -- Pullback (from contravariant fibration)
  module ctrv-fib (fib : is-ctrv-fib) where
    pull : ∀ {x y} → x ~> y → V y → V x
    pull p v = fib p v .center .fst

    colift : ∀ {x y} (p : x ~> y) (v : V y) → E p (pull p v) v
    colift p v = fib p v .center .snd

    colift-unique : ∀ {x y} (p : x ~> y) (v : V y) (u : V x) (e : E p u v)
                  → (pull p v , colift p v) ＝ (u , e)
    colift-unique p v u e = fib p v .paths (u , e)
