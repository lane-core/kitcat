Finite types: type, operations, and properties.

Definitions derived from: Data.Fin.Base, Data.Irr (Amelia Liao et al.; 1lab, January 2026)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin where

open import Core.Data.Fin.Type public hiding (module Fin)

-- Fin, fin, lower, fzero, fsuc at top level

module Fin where
  open Core.Data.Fin.Type.Fin public
  open import Core.Data.Fin.Base public
  open import Core.Data.Fin.Properties renaming (Fin-is-set to set) public

  module impl where
    open import Core.Data.Fin.Impl.Discrete public
    open import Core.Data.Fin.Impl.Trunc public

```
