Lane Biocini
Oct 12th, 2024

Type definitions for our Path type

```

{-# OPTIONS --safe #-}

module Lib.Path.Impl.Typoid where

open import Lib.Prim
open import Lib.Trait.Typoid.Type

open import Lib.Path.Type
open import Lib.Path.Impl.Setoid


path-typd-str : ∀ {u} (A : u type) → typoid-structure (Id A) _≡_
path-typd-str A .typoid-structure.1cell = path-setoid A
path-typd-str A .typoid-structure.2cell = pathp-setoid

path-typd-ax : ∀ {u} (A : u type) → typoid-axioms (path-typd-str A)
path-typd-ax A .typoid-axioms.hcomp {x} {y} {z} {f} {f'} {g} {g'} (path .f) (path .g) = refl
path-typd-ax A .typoid-axioms.assoc {x} {y} {z} (path x) (path y) (path z) = refl
path-typd-ax A .typoid-axioms.eqvl {x} (path .x) = refl
path-typd-ax A .typoid-axioms.eqvr {x} (path .x) = refl
path-typd-ax A .typoid-axioms.invl {x} (path .x) = refl
path-typd-ax A .typoid-axioms.invr {x} (path .x) = refl

path-has-typd : ∀ {u} (A : u type) → has-typoid (Id A) _≡_
path-has-typd A .typd-str = path-typd-str A
path-has-typd A .typd-ax = path-typd-ax A
