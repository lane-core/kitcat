Binary trees with size (internal node count), depth (longest
root-to-leaf path), and left-depth (associativity nesting depth).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Tree.BinTree where

open import Core.Type

open import Data.Tree.Type

BinTree : Type
BinTree = Tree ⊤

pattern leaf⋆ = leaf tt
