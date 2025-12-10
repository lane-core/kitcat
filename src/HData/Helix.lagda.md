From Tesla Zhang's [Two tricks to trivialize higher indexed families](https://arxiv.org/pdf/2309.14187)

```agda

{-# OPTIONS --safe --erased-cubical #-}

module HData.Helix where

open import Lib.Prim
open import Lib.Cubical.Base
open import Lib.Cubical.Kan
open import Lib.Equiv
open import Lib.Path
open import Lib.Path.Gpd renaming (module cat to cat; cat to infixr 40 _∙_)
open import Lib.Path.Homotopy

open import HData.Circle

-- In fording, we move the index to an `x` where instead of pattern matching on
-- a dependent type index the constructor demands a proof that the instance
-- matches the intended rule
data Helix (x : Circle) : Type where
  zero : x ≡ base → Helix x
  succ : ((i : I) → x ≡ loop i) → Helix x

private
  Int : Type
  Int = Helix base
