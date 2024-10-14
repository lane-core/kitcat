Lane Biocini
Oct 12th, 2024

Type definitions for our Path type

```

{-# OPTIONS --safe #-}

module Lib.Path.Impl.Setoid where

open import Lib.Prim
open import Lib.Trait.Setoid
open import Lib.Path.Type
open import Lib.Path.Base
open is-setoid

path-setoid : ∀ {u} (A : u type) → is-setoid (Id A)
path-setoid A .eqv = path
path-setoid A .inv = path-inv
path-setoid A .concat = path-concat

pathp-setoid : ∀ {u} {A : u type}
           → setoid-over (Path {u} {A}) _≡_
pathp-setoid x y = path-setoid (x ≡ y)
