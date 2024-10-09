Lane Biocini

From Rijke's Introduction to Homotopy Type Theory, but this construction
is heavily borrowed from Jon Sterling's implementation in the TypeTopology
module UF.IdentitySystem. Where we build upon his work is in connecting
this with the theory of Typoids.

```

{-# OPTIONS --safe #-}

module Lib.IdSys where

open import Lib.Prim
open import Lib.Rel

record has-id-system {u v} w
 (ob : u type)
 (fam : ob → v type) (a : ob)
 : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  ctr : fam a
  elim : (P : (x : ob) → fam x → w type) {x : ob} (f : fam x)
       → P a ctr → P x f

module _ {u v w} w' (ob : u type) (B : ob → w type) where
 has-dep-id-system : {a : ob} {fam : ob → v type}
  → ([a] : has-id-system  w ob fam a)
  → ((x : ob) (q : fam x) (y : B x) → w' type)
  →  (b : B a) → (w ⊔ w') ⁺ type
 has-dep-id-system {a} [a] fam b = has-id-system w (B a) (fam a ctr) b where
  open has-id-system [a]

record idsys-structure {u} v w (ob : u type) (a : ob) : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  fam : ob → v type
  sys : has-id-system w ob fam a

 open has-id-system sys public

module _ {u v} w w' (ob : u type) (B : ob → w type) where
 record dep-id-system {a : ob}
  ([a] : idsys-structure v w ob a)
  (b : B a)
  : u ⊔ (v ⊔ w ⊔ w') ⁺ type where
  private
   module [a] = idsys-structure [a]
  field
   fam : (x : ob) (q : [a].fam x) (y : B x) → w' type
   sys : has-dep-id-system w' ob B [a].sys fam b

  open has-id-system sys public

record id-system {u} v w (ob : u type) (a : ob) : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  fam : ob → v type
  sys : has-id-system w ob fam a

 open has-id-system sys public

unbiased-id-sys : ∀ {u} v → u type → u ⊔ v ⁺ type
unbiased-id-sys v ob = (a : ob) → idsys-structure v v ob a

module unbiased-id-sys {u v} {ob : u type}
 ([id] : unbiased-id-sys v ob)
 where
 module _ {x : ob} where
  open idsys-structure ([id] x) public

 inv : {x y : ob} → fam {x} y → fam {y} x
 inv {x} p = elim (λ z p → fam {z} x) p ctr
