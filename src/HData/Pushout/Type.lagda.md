The pushout higher inductive type.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Pushout.Type where

open import Core.Type
open import Core.Base

private variable
  ℓa ℓb ℓc : Level

data Pushout {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (f : C → A) (g : C → B) : Type (ℓa ⊔ ℓb ⊔ ℓc) where
  inl  : A → Pushout f g
  inr  : B → Pushout f g
  glue : (c : C) → inl (f c) ≡ inr (g c)
```
