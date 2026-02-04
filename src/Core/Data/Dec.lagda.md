Decidable types, stability lemmas, and Hedberg's theorem.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Dec where

open import Core.Data.Dec.Type public hiding (module Dec)

module Dec where
  open Core.Data.Dec.Type.Dec public
  open import Core.Data.Dec.Base public
  open import Core.Data.Dec.Properties public

```
