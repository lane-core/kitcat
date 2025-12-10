Lane Biocini
October 23, 2025

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Iso where

open import Lib.Type
open import Lib.Sigma
open import Lib.Cubical.Base
open import Lib.Cubical.Kan hiding (fill)
open import Lib.Path
open import Lib.Path.HLevel
open import Lib.Cubical.Sub

private variable
  u v : Level

record is-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    sec : (x : A) → inv (f x) ≡ x
    retr :  (y : B) → f (inv y) ≡ y

  fun = f

_≅_ Iso : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≅ B = Σ {A = A → B} is-qinv
Iso = _≅_

isotofun : ∀ {u v} {A : Type u} {B : Type v} → A ≅ B → A → B
isotofun e = fst e
