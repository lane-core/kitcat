Lane Biocini
Oct 5th, 2024

Definitions for relations

```
{-# OPTIONS --safe #-}

module Lib.Rel.Over where

open import Lib.Prim
open import Lib.Data.Sigma
open import Lib.Rel.Base

rel-over-rel : ∀ {u v} w {ob : u type} → rel v ob → u ⊔ v ⊔ w ⁺ type
rel-over-rel w {ob} _~_ = {x y : ob} → rel w (x ~ y)

module _ {u v w} {ob : u type}
 (_~_ : rel v ob)
 (_≈_ : rel-over-rel w _~_)
 (_∙_ : transitive _~_)
 where
 associative reflexive-over symmetric-over vertical-comp whisker-left whisker-right
  : u ⊔ v ⊔ w type
 associative = {w x y z : ob} → (f : w ~ x) (g : x ~ y) (h : y ~ z)
             → ((f ∙ g) ∙ h) ≈ (f ∙ (g ∙ h))
 reflexive-over = {x y : ob} → reflexive (_≈_ {x} {y})
 symmetric-over = {x y : ob} → symmetric (_≈_ {x} {y})
 vertical-comp = {x y : ob} → transitive (_≈_ {x} {y})

 horizontal-comp = {x y z : ob} {f f' : x ~ y} {g g' : y ~ z}
                 → f ≈ f' → g ≈ g' → (f ∙ g) ≈ (f' ∙ g')

 whisker-left = {x y z : ob} (f : x ~ y) {g h : y ~ z} → g ≈ h → (f ∙ g) ≈ (f ∙ h)
 whisker-right = {x y z : ob} {f g : x ~ y} → f ≈ g → (h : y ~ z) → (f ∙ h) ≈ (g ∙ h)

 module _ (idn : reflexive-over)
  where
  hcomp-to-lwhisker : horizontal-comp → whisker-left
  hcomp-to-lwhisker hcomp = (λ f H → hcomp (idn f) H)

  hcomp-to-rwhisker : horizontal-comp → whisker-right
  hcomp-to-rwhisker hcomp = (λ H h → hcomp H (idn h))

  hcomp-to-whiskers : horizontal-comp → Σ × ꞉ whisker-left , whisker-right
  hcomp-to-whiskers hcomp = hcomp-to-lwhisker hcomp , hcomp-to-rwhisker hcomp

  whiskers-to-hcomp : vertical-comp → whisker-left → whisker-right → horizontal-comp
  whiskers-to-hcomp _●_ lw rw {x} {y} {z} {f} {f'} {g} H K = rw H g ● lw f' K

 module _ (idn : reflexive _~_)
  where
  idn-left idn-left-op idn-right idn-right-op : u ⊔ v ⊔ w type
  idn-left = ∀ {x y} (f : x ~ y) → (idn x ∙ f) ≈ f
  idn-left-op = ∀ {x y} (f : x ~ y) → f ≈ (idn x ∙ f)
  idn-right = ∀ {x y} (f : x ~ y) → (f ∙ idn y) ≈ f
  idn-right-op = ∀ {x y} (f : x ~ y) → f ≈ (f ∙ idn y)

  module _ (inv : symmetric _~_)
   where
   sym-left sym-left-op sym-right sym-right-op : u ⊔ v ⊔ w type
   sym-left = ∀ {x y} (f : x ~ y) → (inv f ∙ f) ≈ idn y
   sym-left-op = ∀ {x y} (f : x ~ y) → idn y ≈ (inv f ∙ f)
   sym-right = ∀ {x y} (f : x ~ y) → (f ∙ inv f) ≈ idn x
   sym-right-op = ∀ {x y} (f : x ~ y) → idn x ≈ (f ∙ inv f)
