Character properties: Eq and Show instances.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Prim.Char.Properties where

open import Core.Type
open import Core.Prim.Char.Type
open import Core.Prim.Char.Base
open import Core.Data.String using (module String)
open import Core.Trait.Eq using (Eq)
open import Core.Trait.Show using (Show)

open String using (String)

instance
  Eq-Char : Eq Char
  Eq-Char .Eq._==_ = char-eq

  Show-Char : Show Char
  Show-Char .Show.show = String.show-char

```

Discrete-Char would require proving injectivity of `to-nat`, which is
not available from builtins under `--safe`. We leave it for future work.
