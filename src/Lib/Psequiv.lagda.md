Lane Biocini
Sept 24th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Psequiv where

open import Lib.Prim
open import Lib.Sigma
open import Lib.Hom
open import Lib.Homotopy

record psEqv {u} v (ob : u type) : u ⊔ v ⁺ type
 where
 constructor mk
 infix 3 inv
 field
  path : ob → ob → v type
  eqv : (a : ob) → path a a
  inv : {a b : ob} → path a b → path b a
  concat : hom.Concat v ob path

 instance
  hom : has-hom v ob
  hom .has-hom.hom = path
  hom .has-hom.id = eqv
  hom .has-hom.comp g f = concat f g

module path where
 module _ {u v} {ob : u type} (path : ob → ob → v type) where
  Eqv : u ⊔ v  type
  Eqv = hom.Idn v ob path

  Concat : u ⊔ v type
  Concat = hom.Concat v ob path

  Inv : u ⊔ v type
  Inv = {x y : ob} → path x y → path y x

 module _ {u v} {ob : u type} (C : has-hom v ob) where
  open has-hom C

  -- If there are back and forth paths over the type of objects, then
  -- that path is given by a psuedo-equivalence relation
  inv-to-pseqv : ({x y : ob} → hom x y → hom y x) → psEqv v ob
  inv-to-pseqv i .psEqv.path = hom
  inv-to-pseqv i .psEqv.eqv = id
  inv-to-pseqv i .psEqv.inv = i
  inv-to-pseqv i .psEqv.concat {x} {y} = concat


 module _ {u v} {ob : u type} (E : psEqv v ob) where
  open psEqv E

  pseqv-to-hom : has-hom v ob
  pseqv-to-hom .has-hom.hom = path
  pseqv-to-hom .has-hom.id = eqv
  pseqv-to-hom .has-hom.comp = λ g f → concat f g

 Path2 : ∀ {u v} w {ob : u type} → hom.Rel v ob → u ⊔ v ⊔ w ⁺ type
 Path2 w {ob} path = {x y : ob} → path x y → path x y → w type

 module _ {u v w} {ob : u type}
  (path : hom.Rel v ob)
  (_≅_ : Path2 w path)
  where
  module inv (eqv : hom.Idn v ob path) (_∙_ : hom.Concat v ob path) (inv : Inv path) where
   l : u ⊔ v ⊔ w type
   l = {x y : ob} (e : path x y) → (inv e ∙ e) ≅ (eqv y)

   r : u ⊔ v ⊔ w type
   r = {x y : ob} (e : path x y) → (e ∙ inv e) ≅ (eqv x)

  Eqv2 : u ⊔ v ⊔ w type
  Eqv2 = {x y : ob} (f : path x y) → f ≅ f

  Inv2 : u ⊔ v ⊔ w type
  Inv2 = {x y : ob} {f g : path x y} → f ≅ g → g ≅ f

  Concat2 : u ⊔ v ⊔ w type
  Concat2 = {x y : ob} {f g h : path x y}
                → f ≅ g → g ≅ h → f ≅ h

  hComp : hom.Concat v ob path → u ⊔ v ⊔ w type
  hComp concat = htpy.hComp w path _≅_ (λ g f → concat f g)

 PathP : ∀ {u v} w {ob : u type} → hom.Rel v ob → u ⊔ v ⊔ w ⁺ type
 PathP w {ob} path = (x y : ob) → psEqv w (path x y)
 module PathP {u v w} {ob : u type} {path : hom.Rel v ob} (P : PathP w path) where
  cons : (pathp : Path2 w path)
           → Eqv2 path pathp
           → Inv2 path pathp
           → Concat2 path pathp
           → PathP w path
  cons pathp idn2 inv2 cc2 x y .psEqv.path = pathp
  cons pathp idn2 inv2 cc2 x y .psEqv.eqv = idn2
  cons pathp idn2 inv2 cc2 x y .psEqv.inv = inv2
  cons pathp idn2 inv2 cc2 x y .psEqv.concat = cc2

  path2 : Path2 w path
  path2 {x} {y} = P x y .psEqv.path

  iso : Eqv2 path path2
  iso {x} {y} = P x y .psEqv.eqv

  inv2 : Inv2 path path2
  inv2 {x} {y} = P x y .psEqv.inv

  concat2 : Inv2 path path2
  concat2 {x} {y} = P x y .psEqv.inv
