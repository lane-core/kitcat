Float properties: Eq and Show instances.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Prim.Float.Properties where

open import Core.Prim.Float.Type
open import Core.Prim.Float.Base
open import Core.Trait.Eq using (Eq)
open import Core.Trait.Show using (Show)

instance
  Eq-Float : Eq Float
  Eq-Float .Eq._==_ = float-eq

  Show-Float : Show Float
  Show-Float .Show.show = show-float

```
