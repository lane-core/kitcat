Join as a pushout.

The join of `A` and `B`, written `A * B`, is the space of formal line
segments from points of `A` to points of `B`. It is the pushout of
the two projections from `A x B`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Pushout.Join where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma

import HData.Pushout.Type as Pushout
open Pushout using (Pushout)
import HData.Pushout.Base as Base

private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  B : Type ℓ'

infixl 6 _⋆_

_⋆_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A ⋆ B = Pushout {C = A × B} fst snd

inl : {A : Type ℓ} {B : Type ℓ'} → A → A ⋆ B
inl = Pushout.inl

inr : {A : Type ℓ} {B : Type ℓ'} → B → A ⋆ B
inr = Pushout.inr

path
  : {A : Type ℓ} {B : Type ℓ'}
  → (a : A) (b : B) → inl a ≡ inr b
path a b = Pushout.glue (a , b)

ind
  : {A : Type ℓ} {B : Type ℓ'} {P : A ⋆ B → Type ℓ''}
  → (l : (a : A) → P (inl a))
  → (r : (b : B) → P (inr b))
  → (p : (a : A) (b : B)
    → PathP (λ i → P (path a b i)) (l a) (r b))
  → (x : A ⋆ B) → P x
ind l r p = Base.ind _ l r (λ { (a , b) → p a b })

rec
  : {A : Type ℓ} {B : Type ℓ'} {X : Type ℓ''}
  → (l : A → X)
  → (r : B → X)
  → (p : (a : A) (b : B) → l a ≡ r b)
  → A ⋆ B → X
rec l r p = Base.rec l r (λ { (a , b) → p a b })

swap
  : {A : Type ℓ} {B : Type ℓ'}
  → A ⋆ B → B ⋆ A
swap = Base.rec Pushout.inr Pushout.inl
  λ { (a , b) → sym (Pushout.glue (b , a)) }
```
