Set quotients as a higher inductive type.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Quotient where

open import HData.Quotient.Type public

module Quotient where
  open import HData.Quotient.Base public
  open import HData.Quotient.Properties public
```
