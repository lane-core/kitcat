Lane Biocini
May 04, 2024

```agda
{-# OPTIONS --safe #-}

module Base.Equiv where

open import Prim.Universe
open import Prim.Pi
open import Prim.Sigma
open import Notation.Reasoning
open import Prim.Id
open import Base.Homotopy


module Map {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} (f : A → B) where
 module sec where
  record is-section : 𝓊 ⊔ 𝓋 type where
   field
    map : B → A
    htpy : f ∘ map ∼ id

  open is-section public

 open sec using (is-section)

 is-retraction : 𝓊 ⊔ 𝓋 type
 is-retraction = Σ map ꞉ (B → A) , map ∘ f ∼ id

 module retr (r : is-retraction) where
  open Σ r renaming (fst to map; snd to htpy) public

 is-equiv : 𝓊 ⊔ 𝓋 type
 is-equiv = is-section × is-retraction

 module is-equiv (e : is-equiv) where
  open Σ e renaming (fst to sec; snd to retr) public

 has-inverse : 𝓊 ⊔ 𝓋 type
 has-inverse = Σ map ꞉ (B → A) , (f ∘ map ∼ id) × (map ∘ f ∼ id)

 module has-inverse (i : has-inverse) where
  open Σ i renaming (fst to map; snd to iso) public
  open Σ iso renaming (fst to left; snd to right) public


 module from where
  inverse : has-inverse → is-equiv
  inverse (map , H , K) .is-equiv.sec .sec.map = map
  inverse (map , H , K) .is-equiv.sec .sec.htpy = H
  inverse (map , H , K) .is-equiv.retr .retr.map = map
  inverse (map , H , K) .is-equiv.retr .retr.htpy = K

open Map public
open is-equiv public

_≃_ : ∀ {𝓊 𝓋} → 𝓊 type → 𝓋 type → 𝓊 ⊔ 𝓋 type
A ≃ B = Σ f ꞉ (A → B) , is-equiv f

Equiv : ∀ 𝓊 𝓋 → 𝓊 type → 𝓋 type → 𝓊 ⊔ 𝓋 type
Equiv 𝓊 𝓋 = _≃_ {𝓊} {𝓋}

id-is-equiv : ∀ {𝓊} {A : 𝓊 type} → is-equiv {𝓊} {𝓊} {A} (id {𝓊})
id-is-equiv .sec .sec.map = id
id-is-equiv .sec .sec.htpy = λ x → Id.refl
id-is-equiv .retr .retr.map = id
id-is-equiv .retr .retr.htpy = λ x → Id.refl

module Equiv where
 rfl : ∀ {𝓊} {A : 𝓊 type} → A ≃ A
 rfl = id , id-is-equiv

 qed : ∀ {𝓊} (A : 𝓊 type) → A ≃ A
 qed A = rfl

 module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} (E : A ≃ B) where
  eqtofun : A → B
  eqtofun = E .is-equiv.map

  inv : B ≃ A
  inv .map = r
  inv .eq .sec .sec.map = map
  inv .eq .sec .sec.htpy = R
  inv .eq .retr .retr.map = map
  inv .eq .retr .retr.htpy = concat (lwhisker map L) S
   where
    open Htpy

    H : r ∘ map ∘ s ∼ r
    H = lwhisker r S

    K : r ∘ map ∘ s ∼ s
    K = rwhisker R s

    L : r ∼ s
    L = λ x → Id.concat (Id.inv (H x)) (K x)

 module _ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : 𝓌 type}
          (D : A ≃ B) (E : B ≃ C)
          where
  module F = equiv D
  module G = equiv E

  concat : A ≃ C
  concat .equiv.map = G.map ∘ F.map
  concat .equiv.eq .sec .sec.map = F.s ∘ G.s
  concat .equiv.eq .sec .sec.htpy =  λ x → Id.concat (H x) (G.S x)
   where
    H : G.map ∘ F.map ∘ F.s ∘ G.s ∼ G.map ∘ G.s
    H = Htpy.lwhisker G.map (Htpy.rwhisker F.S G.s)
  concat .equiv.eq .retr .retr.map = F.r ∘ G.r
  concat .equiv.eq .retr .retr.htpy = λ x → Id.concat (K x) (F.R x)
   where
    K : F.r ∘ G.r ∘ G.map ∘ F.map ∼ F.r ∘ F.map
    K = Htpy.rwhisker (Htpy.lwhisker F.r G.R) F.map

 module _ {𝓊 𝓋 𝓌} {B : 𝓋 type} {C : 𝓌 type} where
  _≃⟨_⟩_ eq-reasoning : Reasoning (λ (X : 𝓊 type) → X ≃ B) (_≃ C) (_≃ C) B
  _≃⟨_⟩_ _ = concat
  eq-reasoning _ = concat

  infixr 7 _≃⟨_⟩_
