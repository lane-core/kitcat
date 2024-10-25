Lane Biocini
Oct 19th, 2024

```

{-# OPTIONS --safe #-}

module Lib.Trait.Setoid.Product where

open import Lib.Prim
open import Lib.Product
open import Lib.Path.Type

open import Lib.Trait.Setoid.Type
open import Lib.Trait.Cut

module _ {u₁ v₁ u₂ v₂} (A : Setoid u₁ v₁) (B : Setoid u₂ v₂) where
 private
  module A = Setoid A
  module B = Setoid B

 Pair-Eqv : A.ob × B.ob → A.ob × B.ob → v₁ ⊔ v₂ type
 Pair-Eqv (x , y) (x' , y') = x A.≃ x' × y B.≃ y'

 Pair-Setoid : Setoid (u₁ ⊔ u₂) (v₁ ⊔ v₂)
 Pair-Setoid .fst = A.ob × B.ob
 Pair-Setoid .snd .is-setoid._≃_ (x , y) (x' , y') = x A.≃ x' × y B.≃ y'
 Pair-Setoid .snd .is-setoid.has-st .has-setoid.eqv x = A.eqv (x .fst) , B.eqv (x .snd)
 Pair-Setoid .snd .is-setoid.has-st .has-setoid.concat p q =
  A.concat (p .fst) (q .fst) , B.concat (p .snd) (q .snd)
 Pair-Setoid .snd .is-setoid.has-st .has-setoid.inv p = A.inv (p .fst) , B.inv (p .snd)

 private module A×B = Setoid Pair-Setoid

 pair-to-eqv : (z w : A.ob × B.ob) → pr₁ z A.≃ pr₁ w × pr₂ z B.≃ pr₂ w → z A×B.≃ w
 pair-to-eqv z w p = p

 eqv-to-pair : (z w : A.ob × B.ob) → z A×B.≃ w → pr₁ z A.≃ pr₁ w × pr₂ z B.≃ pr₂ w
 eqv-to-pair z w p = p

 pair-eta : (w : A×B.ob) {x : A.ob} {y : B.ob}
          → (x , y) A×B.≃ w → (x A.≃ pr₁ w) × (y B.≃ pr₂ w)
 pair-eta w p = p

 pair-eta⁻¹ : (w : A×B.ob) {x : A.ob} {y : B.ob}
            → (x A.≃ pr₁ w) × (y B.≃ pr₂ w) → (x , y) A×B.≃ w
 pair-eta⁻¹ w p = p
