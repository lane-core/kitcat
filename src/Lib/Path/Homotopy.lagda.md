Lane Biocini

The type of homotopies

```agda

{-# OPTIONS --safe  #-}

module Lib.Path.Homotopy where

open import Lib.Prim
open import Lib.Rel
open import Lib.Pi using (Π)

open import Lib.Path.Type
open import Lib.Path.Base

open import Lib.Trait.Setoid

_∼_ : ∀ {u v} {A : u type} {B : A → v type} → (f g : Π B) → u ⊔ v type
_∼_ {u} {v} {A} {B} f g = ∀ e → f e ≡ g e

module _ {u v} {A : u type} {B : A → v type} where
 open is-setoid

 htpy-idn : rel.reflexive (_∼_ {u} {v} {A} {B})
 htpy-idn H = λ e → path (H e)

 htpy-concat : rel.transitive (_∼_ {u} {v} {A} {B})
 htpy-concat H K = λ e → path-concat (H e) (K e)

 htpy-inv : rel.symmetric (_∼_ {u} {v} {A} {B})
 htpy-inv H = λ e → path-inv (H e)

 htpy-setoid : is-setoid (_∼_ {u} {v} {A} {B})
 htpy-setoid .is-setoid.eqv = htpy-idn
 htpy-setoid .is-setoid.inv = htpy-inv
 htpy-setoid .is-setoid.concat = htpy-concat
