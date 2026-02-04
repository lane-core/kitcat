Foldable instance for List.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Impl.Foldable where

open import Core.Data.List.Type
open import Core.Data.List.Base
open import Core.Trait.Effect
open import Core.Trait.Foldable using (Foldable)

instance
  Foldable-List : Foldable (impl List)
  Foldable-List .Foldable.foldr = foldr

```
