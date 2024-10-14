Lane Biocini
Oct 9th, 2024

From Iosif Petrakis's paper [Univalent Typds](https://arxiv.org/abs/2205.06651v1)

```

{-# OPTIONS --safe #-}

module Lib.Trait.Setoid where

open import Lib.Prim
open import Lib.Rel

record is-setoid {u v} {ob : u type} (path : rel v ob) : u ⊔ v ⁺ type where
 field
  eqv : rel.reflexive path
  inv : rel.symmetric path
  concat : rel.transitive path

setoid-over : ∀ {u v w} {ob : u type} (path : rel v ob)
                 → (pathp : rel-over-rel w path)
                 → u ⊔ v ⊔ w ⁺ type
setoid-over {u} {v} {w} {ob} path pathp = (x y : ob) → is-setoid (pathp {x} {y})

module setoid-over {u v w} {ob : u type} {path : rel v ob}
 {pathp : rel-over-rel w path}
 (pathp-eqv : setoid-over path pathp)
 where
 module _ {x y : ob} where
  open is-setoid (pathp-eqv x y)
   renaming (eqv to eqv2 ; inv to inv2; concat to concat2)
   public
