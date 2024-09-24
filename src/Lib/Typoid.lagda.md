Lane Biocini

From Iosif Petrakis's paper [Univalent Typoids](https://arxiv.org/abs/2205.06651v1)

Some modifications for the purposes of this development were made.

```
{-# OPTIONS --safe #-}

module Lib.Typoid where

open import Lib.Prim
open import Lib.Hom
open import Lib.Homotopy
open import Lib.Psequiv

module typoid {u v} w {ob : u type} (E : psEqv v ob) where
 open psEqv E
 record isomorphism : u ⊔ v ⊔ w ⁺ type
  where
  field
   pathp : path.PathP w path

  open path.PathP pathp public
  field
   hcomp : path.hComp path path2 concat

  lwhisk : htpy.whisker.l w path path2 (λ g f → concat f g)
  lwhisk H h = hcomp H (iso h)

  rwhisk : htpy.whisker.r w path path2 (λ g f → concat f g)
  rwhisk f H = hcomp (iso f) H

 record axioms (S : isomorphism): u ⊔ v ⊔ w type
  where
  open isomorphism S
  open htpy w path
  field
   invl : path.inv.l path path2 eqv concat inv
   eqvl : unitor.l path2 (λ g f → concat f g) eqv
   eqvr : unitor.r path2 (λ g f → concat f g) eqv
   assoc : associator path2 (λ g f → concat f g)

record is-typoid {u} v w (ob : u type) : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  has-eq : psEqv v ob
  has-iso : typoid.isomorphism w has-eq
  has-ax : typoid.axioms w has-eq has-iso

 open psEqv has-eq
  renaming ( path to infix 0 path
           ; inv to infix 5 inv
           ; concat to infixl 2 concat
           ) public
 open typoid.isomorphism has-iso
  renaming ( path2 to infix 0 path2
           ; inv2 to infix 5 inv2
           ; concat2 to infixl 2 concat2)
           public

 open typoid.axioms has-ax public
