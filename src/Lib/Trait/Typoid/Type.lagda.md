Lane Biocini
Oct 9th, 2024

From Iosif Petrakis's paper [Univalent Typds](https://arxiv.org/abs/2205.06651v1)

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Type where

open import Lib.Prim
open import Lib.Rel
open import Lib.Data.Sigma using (Σ; Sigma)
open import Lib.Trait.Setoid

module typd where
 record structure {u v w} {ob : u type}
  (_≃_ : ob → ob → v type)
  (_≅_ : ∀ {x y} → x ≃ y → x ≃ y → w type)
  : u ⊔ (v ⊔ w) ⁺ type
  where
  field
   1cell : is-setoid _≃_
   2cell : setoid-over _≃_ _≅_

  open is-setoid 1cell public
  module _ {x y : ob} where
   open is-setoid (2cell x y)
    renaming ( eqv to eqv2
             ; concat to concat2
             ; inv to inv2
             ) public

 record axioms {u v w} {ob : u type}
  {_≃_ : ob → ob → v type}
  {_≅_ : ∀ {x y} → x ≃ y → x ≃ y → w type}
  (S : structure _≃_ _≅_)
  : u ⊔ v ⊔ w type
  where
  open structure S renaming (concat to infixl 40 _∙_)
  field
   hcomp : {x y z : ob} {f f' : x ≃ y} {g g' : y ≃ z}
         → f ≅ f' → g ≅ g' → f ∙ g ≅ f' ∙ g'
   assoc : {w x y z : ob} → (f : w ≃ x) (g : x ≃ y) (h : y ≃ z)
         → (f ∙ g) ∙ h ≅ f ∙ (g ∙ h)
   eqvl : ∀ {x y} (e : x ≃ y) → eqv x ∙ e ≅ e
   eqvr : ∀ {x y} (e : x ≃ y) → e ∙ eqv y ≅ e
   invl : ∀ {x y} (e : x ≃ y) → inv e ∙ e ≅ eqv y
   invr : ∀ {x y} (e : x ≃ y) → (e ∙ inv e) ≅ eqv x

 open structure public
 open axioms public

record has-typoid {u v w} {ob : u type}
 (_≃_ : rel v ob)
 (_≅_ : rel-over-rel w _≃_)
 : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  typd-str : typd.structure _≃_ _≅_
  typd-ax : typd.axioms typd-str

 open typd.structure typd-str public
 open typd.axioms typd-ax public

open has-typoid using (typd-str; typd-ax) public

record is-typoid {u} v w (ob : u type) : u ⊔ (v ⊔ w) ⁺ type
 where
 infix 0 _≃_ _≅_
 field
  _≃_ : rel v ob
  _≅_ : rel-over-rel w _≃_
  has-typd : has-typoid _≃_ _≅_

 open has-typoid has-typd public

Typoid : ∀ u v w → (u ⊔ v ⊔ w) ⁺ type
Typoid u v w = Σ ob ꞉ u type , is-typoid v w ob

module Typoid {u v w} (𝓐 : Typoid u v w) where
 open Σ 𝓐

 ob = fst
 open is-typoid snd
  renaming ( concat to infixl 40 _•_
           ; concat2 to infixl 40 _●_
           ; inv to _⁻¹
           )

 eqv-inv : ∀ x → eqv x ⁻¹ ≅ eqv x
 eqv-inv x = inv2 (eqvl (eqv x ⁻¹)) ● invr (eqv x)

 inv-inv : ∀ {x y} (e : x ≃ y) → e ⁻¹ ⁻¹ ≅ e
 inv-inv {x} {y} e = inv2 (eqvr (e ⁻¹ ⁻¹))
                   ● hcomp (eqv2 (e ⁻¹ ⁻¹)) (inv2 (invl e))
                   ● inv2 (assoc (e ⁻¹ ⁻¹) (e ⁻¹) e)
                   ● hcomp (invl (e ⁻¹)) (eqv2 e)
                   ● eqvl e

 inv-cong : ∀ {x y} (e d : x ≃ y) → e ≅ d → e ⁻¹ ≅ d ⁻¹
 inv-cong {x} {y} e d p = inv2 (eqvr (e ⁻¹))
                        ● hcomp (eqv2 (e ⁻¹)) (inv2 (invr d))
                        ● inv2 (assoc (e ⁻¹) d (d ⁻¹))
                        ● hcomp (inv2 (hcomp (eqv2 (e ⁻¹)) p)) (eqv2 (d ⁻¹))
                        ● hcomp (invl e) (eqv2 (d ⁻¹))
                        ● eqvl (d ⁻¹)


 open is-typoid snd public
