```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Equiv where

open import Prim.Type
open import Prim.Cubical
open import Prop.HLevel
open import Prim.Data.Path
open import Prim.Data.Sigma

open import Data.Path.Type

infix 2 _≃_

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    contr-map : (y : B) → is-contr (fiber f y)

  fun = f

  center : (y : B) → fiber f y
  center y = contr-map y .ctr

  inv : B → A
  inv y = center y .fst

  fibers : {y : B} (fb : fiber f y) → center y ＝ fb
  fibers {y} = contr-map y .paths

  sec : (x : A) → inv (f x) ＝ x
  sec x i = fibers (x , refl) i .fst

  retr :  (y : B) → f (inv y) ＝ y
  retr y = center y .snd

open is-equiv public
  renaming ( fun to eqv-fun
           ; inv to eqv-inv
           ; sec to eqv-sec
           ; retr to eqv-retr )


_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ {A = A → B} is-equiv
{-# BUILTIN EQUIV      _≃_   #-}

Equiv = _≃_

eqvtofun : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqvtofun e = fst e
{-# BUILTIN EQUIVFUN   eqvtofun  #-}

equiv-proof : ∀ {u v} (T : Type u) (A : Type v) (w : T ≃ A) (a : A)
            → ∀ φ (u : Partial φ (fiber (w .fst) a)) → fiber (w .fst) a [ φ ↦ u ]
equiv-proof {u} {v} T A w a = is-contr→extend (contr-map (w .snd) a)

{-# BUILTIN EQUIVPROOF equiv-proof #-}


```
