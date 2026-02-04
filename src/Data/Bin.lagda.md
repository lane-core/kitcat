Binary strings: type, operations, and properties.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Data.Bin where

open import Core.Type
open import Data.Bin.Type public hiding (module Bin)

module Bin where
  open import Data.Bin.Base public
  open import Data.Bin.Properties public

```
