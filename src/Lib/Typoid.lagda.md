Lane Biocini
Oct 9th, 2024

From Iosif Petrakis's paper [Univalent Typoids](https://arxiv.org/abs/2205.06651v1)

```

{-# OPTIONS --safe #-}

module Lib.Typoid where

open import Lib.Prim
open import Lib.Rel

record psuedoequiv {u} v {ob : u type}
 (path : relation v ob)
 : u ⊔ v ⁺ type
 where
 field
  pseqv-idn : rel.reflexive path
  pseqv-inv : rel.symmetric path
  pseqv-concat : rel.transitive path

open psuedoequiv public

-- a slight abuse of notation to denote this "structure", but I wish to break up
-- a very large definition; a typoid expresses a weak 2-groupoid, so that's a
-- lot of line items. I do feel it's fair to distinguish between "structure"
-- composed of operations forming the cell structures, and the coherence axioms
-- expected to be satisfied.
record typoid-structure {u} (ob : u type) : u ⁺ type
 where
 field
  typd-path : relation u ob
  typd-1cell : psuedoequiv u typd-path

 open psuedoequiv typd-1cell
  renaming ( pseqv-idn to typd-eqv
           ; pseqv-inv to typd-inv
           ; pseqv-concat to typd-concat
           ) public

 field
  typd-pathp : rel-over-rel u typd-path
  typd-hcomp : rel.horizontal-comp typd-path typd-pathp typd-concat
  typd-2cell : (x y : ob) → psuedoequiv u (typd-pathp {x} {y})

 module _ {x y : ob} where
  open psuedoequiv (typd-2cell x y)
   renaming ( pseqv-idn to typd-eqv2
            ; pseqv-inv to typd-inv2
            ; pseqv-concat to typd-concat2
            ) public

record typoid-axioms {u} {ob : u type} (str : typoid-structure ob)
 : u ⁺ type
 where
 open typoid-structure str
 field
  typd-assoc : rel.associative typd-path typd-pathp typd-concat
  typd-eqvl : rel.idn.left typd-path typd-pathp typd-concat typd-eqv
  typd-eqvr : rel.idn.right typd-path typd-pathp typd-concat typd-eqv
  typd-invl : rel.sym.left typd-path typd-pathp typd-concat typd-eqv typd-inv
  typd-invr : rel.sym.right typd-path typd-pathp typd-concat typd-eqv typd-inv

record has-typoid {u} (ob : u type) : u ⁺ type
 where
 field
  typd-str : typoid-structure ob
  typd-ax : typoid-axioms typd-str

 open typoid-structure typd-str public
 open typoid-axioms typd-ax public

open has-typoid public

Typoid : ∀ u → u ⁺ type
Typoid u = Σ ob ꞉ u type , has-typoid ob

module typoid {u} (A : Typoid u) where
 open Σ A renaming (fst to obj; snd to typd) public

 private module export (A : Typoid u) where
  open has-typoid typd
   renaming ( typd-path to path
            ; typd-eqv to eqv
            ; typd-inv to inv
            ; typd-concat to concat
            ; typd-eqv2 to eqv2
            ; typd-inv2 to inv2
            ; typd-concat2 to concat2
            ; typd-pathp to pathp
            ; typd-hcomp to hcomp
            ; typd-assoc to assoc
            ; typd-eqvl to eqvl
            ; typd-eqvr to eqvr
            ; typd-invl to invl
            ; typd-invr to invr
            ) public

 module lemma where
  open export A
   renaming ( path to infix 1 _≃_
            ; pathp to infix 1 _≅_
            ; concat to infixl 5 _∙_
            ; concat2 to infixl 4 _●_
            ; inv to infixl 8 _⁻¹
            )

  eqv-inv : ∀ x → eqv x ⁻¹ ≅ eqv x
  eqv-inv x = inv2 (eqvl (eqv x ⁻¹)) ● invr (eqv x)

  inv-inv : ∀ {x y} (e : x ≃ y) → e ⁻¹ ⁻¹ ≅ e
  inv-inv {x} {y} e = inv2 (eqvr (e ⁻¹ ⁻¹))
                    ● hcomp (eqv2 (e ⁻¹ ⁻¹)) (inv2 (invl e))
                    ● inv2 (assoc (e ⁻¹ ⁻¹) (e ⁻¹) e)
                    ● hcomp (invl (e ⁻¹)) (eqv2 e)
                    ● eqvl e

  inv-cong : ∀ {x y} (e d : x ≃ y) → e ≅ d → e ⁻¹ ≅ d ⁻¹
  inv-cong {x} {y} e d p = inv2 (eqvr (e ⁻¹))
                         ● hcomp (eqv2 (e ⁻¹)) (inv2 (invr d))
                         ● inv2 (assoc (e ⁻¹) d (d ⁻¹))
                         ● hcomp (inv2 (hcomp (eqv2 (e ⁻¹)) p)) (eqv2 (d ⁻¹))
                         ● hcomp (invl e) (eqv2 (d ⁻¹))
                         ● eqvl (d ⁻¹)
