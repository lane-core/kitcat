Lane Biocini

```
{-# OPTIONS --safe #-}

module Lib.Hom where

open import Lib.Prim
open import Lib.Sigma

record has-hom {u} v (ob : u type) : u ⊔ v ⁺ type
 where
 constructor mk
 infix 0 hom
 infixr 40 comp
 infixr 0 concat-syntax

 field
  hom : ob → ob → v type
  id : (a : ob) → hom a a
  comp : {a b c : ob} → hom b c → hom a b → hom a c

 concat : {x y z : ob} → hom x y → hom y z → hom x z
 concat f g = comp g f

 concat-syntax : (x : ob) {y z : ob} → hom x y → hom y z → hom x z
 concat-syntax _ = concat

 syntax concat-syntax x p q = x ⟫ p ≡ q

module hom {u} v (ob : u type) where
 Rel : u ⊔ v ⁺ type
 Rel = ob → ob → v type

 Idn : Rel → u ⊔ v type
 Idn hom = (a : ob) → hom a a

 Comp : Rel → u ⊔ v type
 Comp hom = {x y z : ob} → hom y z → hom x y → hom x z

 Concat : Rel → u ⊔ v type
 Concat hom = {x y z : ob} → hom x y → hom y z → hom x z
