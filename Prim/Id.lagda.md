Lane Biocini
March 30th, 2024

revised August 5th, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Id where

infix 4 _≡_

open import Prim.Universe
open import Prim.Pi

open import Global.Arrow
open import Global.Cut
--open import Global.Equivalence
open import Global.Underlying

module Id where
 data rel {𝓊} (A : 𝓊 type) : A → A → 𝓊 type where
  refl : {x : A} → rel A x x

 Id : ∀ {𝓊} {A : 𝓊 type} → A → A → 𝓊 type
 Id {𝓊} {A} = rel A

 lhs rhs : ∀ {𝓊} {A : 𝓊 type} {x y : A} → Id x y → A
 lhs {_} {_} {x} = const x
 rhs {_} {_} {_} {y} = const y

 ind : ∀ {𝓊 𝓋} {A : 𝓊 type} {x : A}
     → (P : (y : A) → Id x y → 𝓋 type)
     → {y : A} (q : Id x y)
     → P x refl → P y q
 ind {_} {_} {A} {x} P {.x} refl = id

 tr : ∀ {𝓊 𝓋} {A : 𝓊 type}
    → (P : A → 𝓋 type)
    → {x y : A} (q : Id x y)
    → P x → P y
 tr P q = ind (λ - r → P (lhs r) → P -) q id

 ap : ∀ {𝓊 𝓋} {A : 𝓊 type} {Y : 𝓋 type}
    → (f : A → Y)
    → {x y : A} → Id x y
    → Id (f x) (f y)
 ap f p = ind (λ - _ → Id (f (lhs p)) (f -)) p refl

 idtofun : ∀ {𝓊} {A B : 𝓊 type} → Id A B → A → B
 idtofun = tr id
  module idtofun where
   id-map-lemma : ∀ {𝓊} {A : 𝓊 type}
                → Id (tr (id {𝓊 ⁺} {𝓊 type}) refl) (id {𝓊} {A})
   id-map-lemma = refl

 idn : ∀ {𝓊} {A : 𝓊 type} (x : A) → Id x x
 idn x = refl

 inv : ∀ {𝓊} {A : 𝓊 type} {x y : A} → Id x y → Id y x
 inv p = tr (λ - → Id - (lhs p)) p refl

 concat : ∀ {𝓊} {A : 𝓊 type} {x y z : A} → Id x y → Id y z → Id x z
 concat p q = tr (Id (lhs p)) q p

open Id using (Id; refl; tr; ap; idtofun) public

_≡_ : ∀ {𝓊} {A : 𝓊 type}
   → A → A → 𝓊 type
_≡_ {𝓊} {A} = Id.rel A
{-# BUILTIN EQUALITY _≡_ #-}
{-# DISPLAY Id.rel A x y = x ≡ y #-}
{-# DISPLAY Id x y = x ≡ y #-}

module _ {𝓊} {A : 𝓊 type} {x y : A} where
 instance
  arrow-Id : Arrow (x ≡ y)
  arrow-Id .src = Id.lhs
  arrow-Id .tgt = Id.rhs

  underlying-Id : Underlying (x ≡ y)
  underlying-Id = record { ℓ = 𝓊 ; ⌞_⌟ = λ _ → A }

module _ {𝓊} {A : 𝓊 type} {y z : A} where
 instance
  cut-Id : Cut A (_≡ y) (λ p → tgt p ≡ z → src p ≡ z)
  cut-Id .seq = Id.concat {𝓊} {A}
