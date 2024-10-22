Lane Biocini
Oct 13th, 2024

Equality Typoid

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Equality where

open import Lib.Prim
open import Lib.Data.Sigma

open import Lib.Trait.Typoid.Type
open import Lib.Trait.Typoid.Base
open import Lib.Trait.Typoid.Function.Type

open import Lib.Path.Type
open import Lib.Path.Impl.Typoid

has-equality-typd : ∀ {u} (A : u type) → has-typoid (Id A) _≡_
has-equality-typd A .typd-str = path-typd-str A
has-equality-typd A .typd-ax = path-typd-ax A

is-equality-typoid : ∀ {u} (A : u type) → is-typoid u u A
is-equality-typoid A .is-typoid._≃_ = _≡_
is-equality-typoid A .is-typoid._≅_ = _≡_
is-equality-typoid A .is-typoid.has-typd = has-equality-typd A

Eq-Typoid : ∀ {u} → u type → Typoid u u u
Eq-Typoid A .fst = A
Eq-Typoid A .snd = is-equality-typoid A
