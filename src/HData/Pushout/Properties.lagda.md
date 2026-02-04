Pushout functoriality and structural properties.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Pushout.Properties where

open import Core.Type
open import Core.Base
open import Core.Kan

open import HData.Pushout.Type as Pushout
open import HData.Pushout.Base as Base

private variable
  ℓ ℓa ℓb ℓc : Level
```


## Span maps

A map of spans induces a map of pushouts.

```agda

record Span-map {A B C A' B' C' : Type ℓ}
  (f : C → A) (g : C → B) (f' : C' → A') (g' : C' → B')
  : Type ℓ where
  field
    map-apex  : C → C'
    map-left  : A → A'
    map-right : B → B'
    comm-left  : (c : C) → map-left (f c) ≡ f' (map-apex c)
    comm-right : (c : C)
      → map-right (g c) ≡ g' (map-apex c)

open Span-map public

map
  : {A B C A' B' C' : Type ℓ}
  → {f : C → A} {g : C → B} {f' : C' → A'} {g' : C' → B'}
  → Span-map f g f' g'
  → Pushout f g → Pushout f' g'
map sm = Base.rec
  (Pushout.inl ∘ sm .map-left)
  (Pushout.inr ∘ sm .map-right)
  λ c → ap Pushout.inl (sm .comm-left c)
    ∙ Pushout.glue (sm .map-apex c)
    ∙ ap Pushout.inr (sym (sm .comm-right c))
```


## Symmetry

```agda

swap
  : {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  → {f : C → A} {g : C → B}
  → Pushout f g → Pushout g f
swap = Base.rec Pushout.inr Pushout.inl
  λ c → sym (Pushout.glue c)
```
