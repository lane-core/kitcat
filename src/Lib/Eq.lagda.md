Lane Biocini

```
{-# OPTIONS --safe #-}

module Lib.Eq where

open import Lib.Prim
open import Lib.Hom
open import Lib.Typoid

record Eq {u} v w (ob : u type) : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  has-typd : is-typoid v w ob

 open is-typoid has-typd
  renaming ( path to _＝_
           ; path2 to _≡_
           ; inv to _⁻¹
           ; concat to _∙_
           ; concat2 to _●_
           ) public

open Eq ⦃ ... ⦄ public
