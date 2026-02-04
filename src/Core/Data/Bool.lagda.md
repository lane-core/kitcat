Booleans: type, operations, and properties.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Bool where

open import Core.Type

module Bool where
  open import Core.Data.Bool.Type public
  open import Core.Data.Bool.Base public
  open import Core.Data.Bool.Properties public

open Bool public
  using (Bool; true; false)

```
