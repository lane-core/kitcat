Lane Biocini

A pragmatic compromise between type theories

```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Core.Equal.Type where

open import Lib.Core.Prim using (Type; Typeω)
open import Lib.Core.Type using (Σ; _,_)

record Equality : Typeω where
  infix 6 _＝_
  infixr 9 _∙_
  field
    _＝_ : ∀ {u} {A : Type u} → A → A → Type u
    refl : ∀ {u} {A : Type u} {x : A} → x ＝ x
    sym : ∀ {u} {A : Type u} {x y : A} → x ＝ y → y ＝ x
    concat : ∀ {u} {A : Type u} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  private _∙_ = concat
  field
    hcat : ∀ {u} {A : Type u} {x y z : A} {e1 d1 : x ＝ y} {e2 d2 : y ＝ z}
         → e1 ＝ d1 → e2 ＝ d2 → e1 ∙ e2 ＝ d1 ∙ d2
    tr : ∀ {u} {A B : Type u} → A ＝ B → A → B
    cong : ∀ {u v} {A : Type u} {B : Type v}
         → (f : A → B) {x y : A} → x ＝ y
         → f x ＝ f y
    Singl-contr : ∀ {u} {A : Type u} {x : A} (y : Σ (λ a → (x ＝ a))) → (x , refl) ＝ y
    transport-path : ∀ {u v} {A : Type u} (x : A) (P : ∀ y → x ＝ y → Type v) (c : P x refl)
                   → tr (cong (λ (x , p) → P x p) (Singl-contr (x , refl))) c ＝ c
