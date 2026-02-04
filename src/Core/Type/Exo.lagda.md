Type universe hierarchy and numeric literals.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Type.Exo where

open import Core.Type

module Exo where
  data Id {u} (A : Exo) (x : A) : A → Exo u where
    refl : Id A x x

```
