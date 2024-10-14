Lane Biocini
Oct 13th, 2024

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Equality where

open import Lib.Prim
open import Lib.Path.Type
open import Lib.Path.Impl.Setoid
open import Lib.Trait.Typoid.Type

path-typd-str : ∀ {u} (A : u type) → typd.structure (Id A) _≡_
path-typd-str A .typd.1cell = path-setoid A
path-typd-str A .typd.2cell = pathp-setoid

path-typd-ax : ∀ {u} (A : u type) → typd.axioms (path-typd-str A)
path-typd-ax A .typd.hcomp {x} {y} {z} {f} {f'} {g} {g'} (path .f) (path .g) = refl
path-typd-ax A .typd.assoc {x} {y} {z} (path x) (path y) (path z) = refl
path-typd-ax A .typd.eqvl {x} (path .x) = refl
path-typd-ax A .typd.eqvr {x} (path .x) = refl
path-typd-ax A .typd.invl {x} (path .x) = refl
path-typd-ax A .typd.invr {x} (path .x) = refl

has-equality-typd : ∀ {u} (A : u type) → has-typoid (Id A) _≡_
has-equality-typd A .typd-str = path-typd-str A
has-equality-typd A .typd-ax = path-typd-ax A

is-equality-typd : ∀ {u} (A : u type) → is-typoid u u A
is-equality-typd A .is-typoid._≃_ = _≡_
is-equality-typd A .is-typoid._≅_ = _≡_
is-equality-typd A .is-typoid.has-typd = has-equality-typd A
