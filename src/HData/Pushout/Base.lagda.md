Indination principles and cocones for pushouts.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Pushout.Base where

open import Core.Type
open import Core.Base
open import Core.Kan hiding (cocone)

open import HData.Pushout.Type

private variable
  ℓ ℓa ℓb ℓc ℓx : Level

ind
  : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  → {f : C → A} {g : C → B}
  → (P : Pushout f g → Type ℓ)
  → (inl* : (a : A) → P (inl a))
  → (inr* : (b : B) → P (inr b))
  → (glue* : (c : C)
    → PathP (λ i → P (glue c i)) (inl* (f c)) (inr* (g c)))
  → (x : Pushout f g) → P x
ind P inl* inr* glue* (inl a)    = inl* a
ind P inl* inr* glue* (inr b)    = inr* b
ind P inl* inr* glue* (glue c i) = glue* c i

rec
  : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  → {f : C → A} {g : C → B}
  → {X : Type ℓx}
  → (inl* : A → X)
  → (inr* : B → X)
  → (glue* : (c : C) → inl* (f c) ≡ inr* (g c))
  → Pushout f g → X
rec inl* inr* glue* (inl a)    = inl* a
rec inl* inr* glue* (inr b)    = inr* b
rec inl* inr* glue* (glue c i) = glue* c i
```


## Cocones

A cocone under the span `A <- C -> B` into `X` packages the
two maps and their coherence.

```agda

record Cocone {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (f : C → A) (g : C → B) (X : Type ℓx)
  : Type (ℓa ⊔ ℓb ⊔ ℓc ⊔ ℓx) where
  field
    inl-cocone  : A → X
    inr-cocone  : B → X
    glue-cocone : (c : C)
      → inl-cocone (f c) ≡ inr-cocone (g c)

open Cocone public

cocone
  : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  → {f : C → A} {g : C → B}
  → Cocone f g (Pushout f g)
cocone .inl-cocone  = inl
cocone .inr-cocone  = inr
cocone .glue-cocone = glue

factor
  : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  → {f : C → A} {g : C → B} {X : Type ℓx}
  → Cocone f g X → Pushout f g → X
factor cc =
  rec (cc .inl-cocone) (cc .inr-cocone) (cc .glue-cocone)
```
