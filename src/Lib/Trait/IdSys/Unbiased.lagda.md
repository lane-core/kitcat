Lane Biocini
Oct 6th, 2024

From Rijke's Introduction to Homotopy Type Theory, but this construction is
heavily borrowed from Jon Sterling's implementation in the TypeTopology module
UF.IdentitySystem. Where we build upon his work is in connecting this with the
theory of Typoids.

```

{-# OPTIONS --safe #-}

module Lib.Trait.IdSys.Unbiased where

open import Lib.Prim
open import Lib.Data.Sigma
open import Lib.Trait.IdSys.Type
open import Lib.Trait.Setoid

unbiased-id-sys : ∀ {u} v → u type → u ⊔ v ⁺ type
unbiased-id-sys v ob = (a : ob) → id-sys v ob a

module unbiased-id-sys {u v} {ob : u type}
 ([id] : unbiased-id-sys v ob)
 where
 module _ (x : ob) where
  open id-sys ([id] x) using (fam) public

 module _ {x : ob} where
  open id-sys ([id] x) hiding (fam) public

 idn : (x : ob) → fam x x
 idn x = ctr

 inv : {x y : ob} → fam x y → fam y x
 inv {x} p = tr (λ z → fam z x) p ctr

 concat : {x y z : ob} → fam x y → fam y z → fam x z
 concat {x} p q = tr (λ w → fam x w) q p

 setoid : has-setoid fam
 setoid .has-setoid.eqv = idn
 setoid .has-setoid.inv = inv
 setoid .has-setoid.concat = concat

unbiased-htpy-sys : ∀ {u v} (ob : u type)
                  → ([id] : unbiased-id-sys v ob) → u ⊔ v ⁺ type
unbiased-htpy-sys {u} {v} ob [id] = (x y : ob) → unbiased-id-sys v (fam x y)
 where open unbiased-id-sys [id]

module unbiased-htpy-sys {u v} {ob : u type}
 ([id] : unbiased-id-sys v ob)
 ([htpy] : unbiased-htpy-sys ob [id])
 where
 open unbiased-id-sys [id] hiding (setoid)
 module htpy {x} {y} = unbiased-id-sys ([htpy] x y)

 cell : {x y : ob} → fam x y → fam x y → v type
 cell {x} {y} f = id-sys.fam ([htpy] x y f)

 setoid : setoid-over fam cell
 setoid x y = unbiased-id-sys.setoid ([htpy] x y)
