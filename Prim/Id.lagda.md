Lane Biocini
March 30th, 2024

revised August 5th, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Id where

infixr -1 tr
infix 4 _≡_

open import Prim.Universe
open import Prim.Pi

open import Global.Arrow
open import Global.Cut
open import Global.Underlying

data Id {𝓊} (A : 𝓊 type) : A → A → 𝓊 type where
 refl : {x : A} → Id A x x

_≡_ : ∀ {𝓊} {A : 𝓊 type}
   → A → A → 𝓊 type
_≡_ {𝓊} {A} = Id A
{-# BUILTIN EQUALITY _≡_ #-}
{-# DISPLAY Id A x y = x ≡ y #-}

ind : ∀ {𝓊 𝓋} {A : 𝓊 type} {x : A}
    → (P : (y : A) → x ≡ y → 𝓋 type)
    → {y : A} (q : x ≡ y)
    → P x refl → P y q
ind {_} {_} {A} {x} P {.x} refl = id

module _ {𝓊} {A : 𝓊 type} {x y : A} where
 lhs rhs : x ≡ y → A
 lhs p = x
 rhs p = y

 instance
  arrow-Id : Arrow (x ≡ y)
  arrow-Id .src = lhs
  arrow-Id .tgt = rhs

  underlying-Id : Underlying (x ≡ y)
  underlying-Id .Underlying.ℓ = 𝓊
  underlying-Id ._̣ = λ _ → A

tr : ∀ {𝓊 𝓋} {A : 𝓊 type}
   → (P : A → 𝓋 type)
   → {x y : A} (q : x ≡ y)
   → P x → P y
tr P q = ind (λ - r → P (lhs r) → P -) q id

syntax tr A p a = A ∫ p , a

ap : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type}
   → (f : A → B)
   → {x y : A} → x ≡ y → f x ≡ f y
ap f p = ind (λ - _ → f (lhs p) ≡ f -) p refl

idn : ∀ {𝓊} {A : 𝓊 type} (x : A) → x ≡ x
idn x = refl

inv : ∀ {𝓊} {A : 𝓊 type} {x y : A} → x ≡ y → y ≡ x
inv p = tr (_≡ lhs p) p refl

concat : ∀ {𝓊} {A : 𝓊 type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
concat p q = tr (lhs p ≡_) q p

idtofun : ∀ {𝓊} {A B : 𝓊 type} → A ≡ B → A → B
idtofun {𝓊} {A} {B} = tr id
 module idtofun where
  id-map-lemma : ∀ {𝓊} {A : 𝓊 type}
               → tr (id {𝓊 ⁺} {𝓊 type}) refl ≡ id {𝓊} {A}
  id-map-lemma = refl

idtofun⁻¹ : ∀ {𝓊} {A B : 𝓊 type} → A ≡ B → B → A
idtofun⁻¹ p = idtofun (inv p)

module _ {𝓊} {A : 𝓊 type} {y z : A} where
 instance
  cut-Id : Cut A (_≡ y) (λ p → tgt p ≡ z → src p ≡ z)
  cut-Id .seq = concat {𝓊} {A}
