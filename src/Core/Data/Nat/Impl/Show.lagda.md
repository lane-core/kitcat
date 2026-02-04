Show instance for Nat.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Nat.Impl.Show where

open import Core.Data.Nat.Type
open import Core.Trait.Show
open import Core.Data.String using (module String)

instance
  Show-Nat : Show Nat
  Show-Nat .show = String.show-nat

```
