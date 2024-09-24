Lane Biocini

```
{-# OPTIONS --safe #-}

module Lib.Homotopy where

open import Lib.Prim
open import Lib.Hom

module htpy {u v} w {ob : u type} (hom : hom.Rel v ob) where
 module _ (hom : hom.Rel v ob) where
  Htpy : u ⊔ v ⊔ w ⁺ type
  Htpy = ∀ {x y} → hom.Rel w (hom x y)

 module _ (_⇒_ : Htpy hom) where
  Idn2 : u ⊔ v ⊔ w type
  Idn2 = ∀ {x y} → hom.Idn w (hom x y) _⇒_

  Comp2 : u ⊔ v ⊔ w type
  Comp2 = ∀ {x y} → hom.Comp w (hom x y) _⇒_

  hComp : hom.Comp v ob hom → u ⊔ v ⊔ w type
  hComp _∘_ = {x y z : ob} {f f' : hom x y} {g g' : hom y z}
        → f ⇒ f' → g ⇒ g' → (g ∘ f) ⇒ (g' ∘ f')

  module _ (_∘_ : hom.Comp v ob hom) where
   -- Identity laws for 1-cells
   module unitor (id : hom.Idn v ob hom) where
    l : u ⊔ v ⊔ w type
    l = {x y : ob} → (f : hom x y) → (id y ∘ f) ⇒ f
    module l where
     inv : u ⊔ v ⊔ w type
     inv = {x y : ob} → (f : hom x y) →  f ⇒ (id y ∘ f)

    r : u ⊔ v ⊔ w type
    r = {x y : ob} → (f : hom x y) → (f ∘ id x) ⇒ f
    module r where
     inv : u ⊔ v ⊔ w type
     inv = {x y : ob} → (f : hom x y) →  f ⇒ (f ∘ id x)

   -- Associativity of 1-cell composition
   associator : u ⊔ v ⊔ w type
   associator = {x y z w : ob} (h : hom x y) (g : hom y z) (f : hom z w)
              → ((f ∘ g) ∘ h) ⇒ (f ∘ (g ∘ h))
   module associator where
    inv : u ⊔ v ⊔ w type
    inv = {x y z w : ob} (h : hom x y) (g : hom y z) (f : hom z w)
        → (f ∘ (g ∘ h)) ⇒ ((f ∘ g) ∘ h)

   -- Whiskering: composing 1-cells with 2-cells
   module whisker where
    l : u ⊔ v ⊔ w type
    l = {x y z : ob} {f g : hom x y} → f ⇒ g → (h : hom y z) → (h ∘ f) ⇒ (h ∘ g)

    r : u ⊔ v ⊔ w type
    r = {x y z : ob} (f : hom x y) {g h : hom y z} → g ⇒ h → (g ∘ f) ⇒ (h ∘ f)

-- module trlevel {u v} {ob : u type} (C : has-hom v ob) where
--   open has-hom C
--   0-truncated : (E : pseqv C) → u ⊔ v type
--   0-truncated E = Σ c ꞉ ob , ((x : ob) → c ≃ x) where
--    open pseqv E renaming (path to _≃_)

--   --1-truncated : (E : has-pseqv-relation C)
