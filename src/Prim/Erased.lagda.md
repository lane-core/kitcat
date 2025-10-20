```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Prim.Erased where

open import Prim.Type

record Erased {u} (@0 A : Type u) : Type u where
  constructor erase
  field
    @0 erased : A
