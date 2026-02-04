String representation trait.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Show where

open import Core.Type
open import Core.Data.String using (module String)
open import Core.Data.Bool

open String using (String)

private variable
  u : Level
  A : Type u

```

Converts values to string representation, following Idris2/Haskell conventions.

```agda

record Show {u} (A : Type u) : Type u where
  no-eta-equality
  field
    show : A → String

open Show ⦃ ... ⦄ public
{-# INLINE Show.constructor #-}

```

```agda

instance
  Show-Bool : Show Bool
  Show-Bool .show true = "true"
  Show-Bool .show false = "false"

  Show-String : Show String
  Show-String .show = id

```
