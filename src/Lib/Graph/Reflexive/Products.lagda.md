```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Lib.Graph.Reflexive.Base

module Lib.Graph.Reflexive.Products {u v} (R : Rx u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Path
open import Lib.Graph.Reflexive.Base
open import Lib.Graph.Reflexive.Displayed R
open import Lib.Graph.Reflexive.Total R

open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Π-type: sections of displayed structure
-- Vertices are dependent functions, edges are pointwise
Π-Rx : ∀ {w z} (V : Vtx w) (E : Edge z V) (dr : DRefl E) → Rx (u ⊔ w) (u ⊔ z)
Π-Rx V E dr .Rx.₀ = ∀ x → V x
Π-Rx V E dr .Rx.₁ s t = ∀ x → E (ρ x) (s x) (t x)
Π-Rx V E dr .Rx.ρ s x = dr x (s x)

-- Product preserves univalence (requires funext)
-- Π-preserves-univalent : ∀ {w z} {V : Vtx w} {E : Edge z V} {dr : DRefl E}
--                        → is-disp-univalent E
--                        → rx.is-univalent (Π-Rx V E dr)
-- Π-preserves-univalent disp-univ s x y = λ i → {!!}

-- Σ-type of displayed structure (same as total)
Σ-Rx : ∀ {w z} (V : Vtx w) (E : Edge z V) (dr : DRefl E) → Rx (u ⊔ w) (v ⊔ z)
Σ-Rx = tot

-- -- Coproduct over a type family
-- ∐-Rx : ∀ {ℓ w z} {A : Type ℓ} (B : A → Rx w z) → Rx (ℓ ⊔ w) z
-- ∐-Rx {A = A} B .Rx.₀ = Σ a ∶ A , Rx.₀ (B a)
-- ∐-Rx {A = A} B .Rx.₁ (a , x) (b , y) = Σ p ∶ (a ＝ b) , Rx.₁ (B a) x (subst (Rx.₀ ∘ B) p y)
-- ∐-Rx {A = A} B .Rx.ρ (a , x) = refl , Rx.ρ (B a) x

open import Lib.Graph.Reflexive.Constant R

-- Binary product: R ×ᴿ S as total of constant displayed
Binary-product : ∀ {w z} → Rx w z → Rx (u ⊔ w) (v ⊔ z)
Binary-product s = tot (const-vtx s) (const-edge s) (const-drefl s)

-- Projections
π₁ : ∀ {w z} {S : Rx w z} → Rx.₀ (Binary-product R) → Ob
π₁ = fst

π₂ : ∀ {w z} {S : Rx w z} → Rx.₀ (Binary-product S) → Rx.₀ S
π₂ = snd

-- Binary product preserves univalence
-- ×ᴿ-preserves-univalent : ∀ {w z} {S : Rx w z}
--                         → rx.is-univalent R
--                         → rx.is-univalent S
--                         → rx.is-univalent {!!}
-- ×ᴿ-preserves-univalent R-univ S-univ = {!!}
