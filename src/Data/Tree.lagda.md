Polymorphic binary trees: type, operations, and properties.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Data.Tree where

open import Core.Type
open import Data.Tree.Type public hiding (module Tree)

module Tree where
  open import Data.Tree.Base public
  open import Data.Tree.Properties public

```
