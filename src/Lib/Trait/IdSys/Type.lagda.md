Lane Biocini
Oct 6th, 2024

From Rijke's Introduction to Homotopy Type Theory, but this construction is
heavily borrowed from Jon Sterling's implementation in the TypeTopology module
UF.IdentitySystem. Where we build upon his work is in connecting this with the
theory of Typoids.

```

{-# OPTIONS --safe #-}

module Lib.Trait.IdSys.Type where

open import Lib.Prim
open import Lib.Data.Sigma
open import Lib.Trait.Setoid

module _ {u w} {ob : u type} where
 has-id-sys : (fam : ob → w type) (a : ob) → u ⊔ w ⁺ type
 has-id-sys fam a = Σ ctr ꞉ fam a
           , ((P : (x : ob) → fam x → w type) {x : ob} (f : fam x) → P a ctr → P x f)

 module has-id-sys {fam : ob → w type} {a : ob}
  (sys : has-id-sys fam a)
  where
  open Σ sys renaming (fst to ctr; snd to ind) public

  tr : (P : ob → w type) {x : ob} → fam x → P a → P x
  tr P = ind λ x p → P x

record id-sys {u} v (ob : u type) (a : ob) : u ⊔ v ⁺ type
 where
 field
  fam : ob → v type
  sys : has-id-sys fam a

 open has-id-sys sys public
