Lane Biocini
Oct 5th, 2024

Definitions for relations

```
{-# OPTIONS --safe #-}

module Lib.Rel where

open import Lib.Prim
open import Lib.Sigma

relation : ∀ {u} v → u type → u ⊔ v ⁺ type
relation v ob = ob → ob → v type

rel-over-rel : ∀ {u v} w {ob : u type} → relation v ob → u ⊔ v ⊔ w ⁺ type
rel-over-rel w {ob} _~_ = {x y : ob} → relation w (x ~ y)

module rel where
 module _ {u v} {ob : u type}
  (_~_ : relation v ob)
  where
  reflexive = (x : ob) → x ~ x
  transitive = {x y z : ob} → x ~ y → y ~ z → x ~ z
  symmetric = {x y : ob} → x ~ y → y ~ x

 module _ {u v w} {ob : u type}
  (_~_ : relation v ob)
  (_≈_ : {x y : ob} → relation w (x ~ y))
  (_∙_ : transitive _~_)
   where
   associative = {w x y z : ob} → (f : w ~ x) (g : x ~ y) (h : y ~ z)
               → ((f ∙ g) ∙ h) ≈ (f ∙ (g ∙ h))

 module _ {u v w} {ob : u type}
  (_~_ : relation v ob)
  (_≈_ : rel-over-rel w _~_)
  (_∙_ : transitive _~_)
  where
  reflexive-over = {x y : ob} → reflexive (_≈_ {x} {y})
  horizontal-comp = {x y z : ob} {f f' : x ~ y} {g g' : y ~ z}
                  → f ≈ f' → g ≈ g' → (f ∙ g) ≈ (f' ∙ g')

  vertical-comp = {x y : ob} → transitive (_≈_ {x} {y})

  module whisker where
   left = {x y z : ob} (f : x ~ y) {g h : y ~ z} → g ≈ h → (f ∙ g) ≈ (f ∙ h)
   right = {x y z : ob} {f g : x ~ y} → f ≈ g → (h : y ~ z) → (f ∙ h) ≈ (g ∙ h)

   record axioms : u ⊔ v ⊔ w type
    where
    field
     _◁_ : left
     _▷_ : right

  module _ (idn : reflexive-over) where
   hcomp-to-lwhisker : horizontal-comp → whisker.left
   hcomp-to-lwhisker hcomp = (λ f H → hcomp (idn f) H)

   hcomp-to-rwhisker : horizontal-comp → whisker.right
   hcomp-to-rwhisker hcomp = (λ H h → hcomp H (idn h))

   hcomp-to-vcomp : horizontal-comp → whisker.right
   hcomp-to-vcomp hcomp = (λ H h → hcomp H (idn h))

   hcomp-to-whiskers : horizontal-comp → whisker.left × whisker.right
   hcomp-to-whiskers hcomp = hcomp-to-lwhisker hcomp , hcomp-to-rwhisker hcomp

   whiskers-to-hcomp : vertical-comp → whisker.left → whisker.right → horizontal-comp
   whiskers-to-hcomp _●_ lw rw {x} {y} {z} {f} {f'} {g} H K = rw H g ● lw f' K

 module _ {u v w} {ob : u type}
  (_~_ : relation v ob)
  (_≈_ : rel-over-rel w _~_)
  (_∙_ : transitive _~_)
  (idn : reflexive _~_)
  where

  module idn where
   left = ∀ {x y} (g : x ~ y) → (idn x ∙ g) ≈ g
   module left where op = ∀ {x y} (g : x ~ y) → g ≈ (idn x ∙ g)

   right = ∀ {x y} (f : x ~ y) → (f ∙ idn y) ≈ f
   module right where op = ∀ {x y} (f : x ~ y) → f ≈ (f ∙ idn y)

   record axioms : u ⊔ v ⊔ w type
    where
    field
     idnl : left
     idnr : right

    record op : u ⊔ v ⊔ w type
     where
     field
      idnl : left.op
      idnr : right.op

  module sym (inv : symmetric _~_) where
   left = ∀ {x y} (f : x ~ y) → (inv f ∙ f) ≈ idn y
   module left where op = ∀ {x y} (f : x ~ y) → idn y ≈ (inv f ∙ f)

   right = ∀ {x y} (f : x ~ y) → (f ∙ inv f) ≈ idn x
   module right where op = ∀ {x y} (f : x ~ y) → idn x ≈ (f ∙ inv f)

   record axioms : u ⊔ v ⊔ w type
    where
    field
     invl : left
     invr : right

    record op : u ⊔ v ⊔ w type
     where
     field
      invl : left.op
      invr : right.op
