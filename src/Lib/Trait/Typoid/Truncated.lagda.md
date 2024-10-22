Lane Biocini
Oct 9th, 2024

From Iosif Petrakis's paper [Univalent Typds](https://arxiv.org/abs/2205.06651v1)

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Type where

open import Lib.Prim
open import Lib.Rel.Base
open import Lib.Rel.Over

open import Lib.Data.Sigma using (Σ; Sigma)

open import Lib.Trait.Cut
open import Lib.Trait.Setoid

record typoid-structure {u v w} {ob : u type}
 (_≃_ : rel v ob)
 (_≅_ : ∀ {x y} → x ≃ y → x ≃ y → w type)
 : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  1cell : has-setoid _≃_
  2cell : setoid-over _≃_ _≅_

 open has-setoid 1cell public
 module _ {x y : ob} where
  open has-setoid (2cell x y)
   renaming ( eqv to eqv2
            ; concat to concat2
            ; inv to inv2
            ; setoid-cut to typoid-cut
            ) public

record typoid-axioms {u v w} {ob : u type}
 {_≃_ : rel v ob}
 {_≅_ : ∀ {x y} → x ≃ y → x ≃ y → w type}
 (S : typoid-structure _≃_ _≅_)
 : u ⊔ v ⊔ w type
 where
 open typoid-structure S renaming (concat to infixl 40 _•_)
 field
  hcomp : {x y z : ob} {f f' : x ≃ y} {g g' : y ≃ z}
        → f ≅ f' → g ≅ g' → f • g ≅ f' • g'
  assoc : {w x y z : ob} → (f : w ≃ x) (g : x ≃ y) (h : y ≃ z)
        → (f • g) • h ≅ f • (g • h)
  eqvl : ∀ {x y} (e : x ≃ y) → eqv x • e ≅ e
  eqvr : ∀ {x y} (e : x ≃ y) → e • eqv y ≅ e
  invl : ∀ {x y} (e : x ≃ y) → inv e • e ≅ eqv y
  invr : ∀ {x y} (e : x ≃ y) → (e • inv e) ≅ eqv x

record has-typoid {u v w} {ob : u type}
 (_≃_ : rel v ob)
 (_≅_ : rel-over-rel w _≃_)
 : u ⊔ (v ⊔ w) ⁺ type
 where
 field
  typd-str : typoid-structure _≃_ _≅_
  typd-ax : typoid-axioms typd-str

 open typoid-structure typd-str public
 open typoid-axioms typd-ax public

open has-typoid using (typd-str; typd-ax) public

record is-typoid {u} v w (ob : u type) : u ⊔ (v ⊔ w) ⁺ type
 where
 infix 0 _≃_ _≅_
 field
  _≃_ : rel v ob
  _≅_ : rel-over-rel w _≃_
  has-typd : has-typoid _≃_ _≅_

 open has-typoid has-typd public

 instance
  1-typoid : has-setoid _≃_
  1-typoid = 1cell

  2-typoid : {x y : ob} → has-setoid (_≅_ {x} {y})
  2-typoid {x} {y} = 2cell x y

module _ {u v w} {ob : u type}
 {_≃_ : rel v ob}
 {_≅_ : rel-over-rel w _≃_}
 (1t : has-setoid _≃_)
 (2t : setoid-over _≃_ _≅_)
 where
 open has-setoid 1t renaming (concat to infix 40 _•_)
 module _
  (hcomp : {x y z : ob} {f f' : x ≃ y} {g g' : y ≃ z}
         → f ≅ f' → g ≅ g' → (f • g) ≅ (f' • g'))
  (assoc : {w x y z : ob} → (f : w ≃ x) (g : x ≃ y) (h : y ≃ z)
         → ((f • g) • h) ≅ (f • (g • h)))
  (eqvl : ∀ {x y} (e : x ≃ y) → (eqv x • e) ≅ e)
  (eqvr : ∀ {x y} (e : x ≃ y) → (e • eqv y) ≅ e)
  (invl : ∀ {x y} (e : x ≃ y) → (inv e • e) ≅ eqv y)
  (invr : ∀ {x y} (e : x ≃ y) → (e • inv e) ≅ eqv x)
  where
  open typoid-structure
  mk-typoid : is-typoid v w ob
  mk-typoid .is-typoid._≃_ = _≃_
  mk-typoid .is-typoid._≅_ = _≅_
  mk-typoid .is-typoid.has-typd .typd-str .1cell = 1t
  mk-typoid .is-typoid.has-typd .typd-str .2cell = 2t
  mk-typoid .is-typoid.has-typd .typd-ax = record
                                            { hcomp = hcomp
                                            ; assoc = assoc
                                            ; eqvl = eqvl
                                            ; eqvr = eqvr
                                            ; invl = invl
                                            ; invr = invr
                                            }
