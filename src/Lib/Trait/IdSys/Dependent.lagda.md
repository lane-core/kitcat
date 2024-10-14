Lane Biocini
Oct 6th, 2024

From Rijke's Introduction to Homotopy Type Theory, but this construction is
heavily borrowed from Jon Sterling's implementation in the TypeTopology module
UF.IdentitySystem. Where we build upon his work is in connecting this with the
theory of Typoids.

```

{-# OPTIONS --safe #-}

module Lib.Trait.IdSys.Dependent where

open import Lib.Prim
open import Lib.Data.Sigma
open import Lib.Trait.IdSys.Type

module _ {u v w} w' {ob : u type} where
 dep-id-sys : (B : ob → v type) {a : ob}
            → ([a] : id-sys w ob a) (b : B a) → u ⊔ v ⊔ w ⊔ w' ⁺ type
 dep-id-sys B {a} [a] b = Σ fam ꞉ ({x : ob} (q : Id x) (y : B x) → w' type)
                        , has-id-sys (fam ctr) b
  where open id-sys [a] renaming (fam to Id)

module dep-id-sys {u v w w'} {ob : u type}
 {B : ob → v type} {a : ob}
 ([a] : id-sys w ob a) {b : B a}
 (dsys : dep-id-sys w' B [a] b)
   where
    open Σ dsys renaming (fst to famd; snd to sysd) public
    open has-id-sys sysd
     renaming ( ctr to ctrd
              ; ind to indd
              ; tr to trd) public
