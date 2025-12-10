```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.So where

open import Lib.Type
open import Lib.Cubical.Base
open import Lib.Bool

record So (b : Bool) : Type where
  field
    @0 oh : b ≡ tt
