Re-exports of all Core trait modules.

This module collects all traits in the Core.Trait.* namespace for convenient
import. Traits provide automation for common type class patterns following
Idris2 Prelude conventions with 1lab instance resolution patterns.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait where

-- Effect hierarchy
open import Core.Trait.Effect public
open import Core.Trait.Map public
open import Core.Trait.Applicative public
open import Core.Trait.Monad public
open import Core.Trait.Alternative public

-- Container operations
open import Core.Trait.Foldable public
open import Core.Trait.Traversable public

-- Basic traits
open import Core.Trait.Eq public
open import Core.Trait.Ord public
open import Core.Trait.Show public
open import Core.Trait.Cast public

-- Algebraic structures
open import Core.Trait.Semigroup public
open import Core.Trait.Monoid public
open import Core.Trait.Group public
open import Core.Trait.Num public

-- Other
open import Core.Trait.Decidable public
open import Core.Trait.Trunc public
open import Core.Trait.Graphical public
open import Core.Trait.Bifunctor public

-- Underlying stays in Core.Type (root module constraint) but is re-exported here
open import Core.Type public using (Underlying; ℓ-underlying; ⌞_⌟; Underlying-Type; Underlying-Lift)
```
