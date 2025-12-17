```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.So where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Bool

record So (b : Bool) : Type where
  field
    @0 oh : b ≡ tt
