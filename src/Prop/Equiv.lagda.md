```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prop.Equiv where

open import Lib.Type
open import Lib.Path
open import Prop.HLevel

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  field
    contr-map : (y : B) → is-contr (fiber f y)


```
