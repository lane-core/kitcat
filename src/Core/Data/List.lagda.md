List operations and trait instances.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List where

open import Core.Data.List.Type public

module List where
  open import Core.Data.List.Base public
  open import Core.Data.List.Properties public

  module impl where
    open import Core.Data.List.Impl.Map public
    open import Core.Data.List.Impl.Applicative public
    open import Core.Data.List.Impl.Monad public
    open import Core.Data.List.Impl.Alternative public
    open import Core.Data.List.Impl.Foldable public

```
