Lane Biocini
Oct 9th, 2024

From Iosif Petrakis's paper [Univalent Typoids](https://arxiv.org/abs/2205.06651v1)

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Base where

open import Lib.Prim
open import Lib.Rel.Base using (rel)
open import Lib.Data.Sigma using (Σ; Sigma)

open import Lib.Trait.Cut
open import Lib.Trait.Typoid.Type

Typoid : ∀ u v w → (u ⊔ v ⊔ w) ⁺ type
Typoid u v w = Σ ob ꞉ u type , is-typoid v w ob

module Typoid {u v w} (𝓐 : Typoid u v w) where
 open Σ 𝓐

 ob = fst
 open is-typoid snd
  renaming (inv to infix 50 _⁻¹)

 eqv-inv : ∀ x → eqv x ⁻¹ ≅ eqv x
 eqv-inv x = eqv x ⁻¹     ⟩ inv2 (eqvl (eqv x ⁻¹))
           ≡ invr (eqv x)

 inv-inv : ∀ {x y} (e : x ≃ y) → e ⁻¹ ⁻¹ ≅ e
 inv-inv {x} {y} e = e ⁻¹ ⁻¹              ⟩ inv2 (eqvr (e ⁻¹ ⁻¹))
                   ≡ e ⁻¹ ⁻¹ ∙ eqv y      ⟩ hcomp (eqv2 (e ⁻¹ ⁻¹)) (inv2 (invl e))
                   ≡ e ⁻¹ ⁻¹ ∙ (e ⁻¹ ∙ e) ⟩ inv2 (assoc (e ⁻¹ ⁻¹) (e ⁻¹) e)
                   ≡ e ⁻¹ ⁻¹ ∙ e ⁻¹ ∙ e   ⟩ hcomp (invl (e ⁻¹)) (eqv2 e)
                   ≡ eqvl e

 inv-cong : ∀ {x y} (e d : x ≃ y) → e ≅ d → e ⁻¹ ≅ d ⁻¹
 inv-cong {x} {y} e d p = e ⁻¹              ⟩ inv2 (eqvr (e ⁻¹))
                        ≡ e ⁻¹ ∙ eqv x      ⟩ hcomp (eqv2 (e ⁻¹)) (inv2 (invr d))
                        ≡ e ⁻¹ ∙ (d ∙ d ⁻¹) ⟩ inv2 (assoc (e ⁻¹) d (d ⁻¹))
                        ≡ e ⁻¹ ∙ d ∙ d ⁻¹   ⟩ hcomp (inv2 (hcomp (eqv2 (e ⁻¹)) p)) (eqv2 (d ⁻¹))
                        ≡ e ⁻¹ ∙ e ∙ d ⁻¹   ⟩ hcomp (invl e) (eqv2 (d ⁻¹))
                        ≡ eqvl (d ⁻¹)

 open is-typoid snd public
