```
{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Cast where

open import Lib.Type

record Cast {u v} (S : Type u) (T : Type v) : Type (u ⊔ v) where
  constructor MkCast
  field
    cast : S → T

open Cast ⦃ ... ⦄ public
{-# INLINE MkCast #-}
{-# DISPLAY Cast.cast _ = cast #-}
