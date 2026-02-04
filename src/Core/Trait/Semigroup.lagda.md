Semigroup trait: types with an associative binary operation.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Semigroup where

open import Core.Type
open import Core.Base using (_≡_; refl)

private variable
  u : Level
  A : Type u

```

## Semigroup Trait

A semigroup bundles an associative binary operation with its law. The `@0`
annotation makes the associativity proof erased at runtime (compatible with
`--erased-cubical`), while still requiring it when constructing instances.

```agda

record Semigroup {u} (A : Type u) : Type u where
  no-eta-equality
  infixr 6 _<>_
  field
    _<>_ : A → A → A
    @0 sassoc : (x y z : A) → (x <> y) <> z ≡ x <> (y <> z)

open Semigroup ⦃ ... ⦄ public
{-# INLINE Semigroup.constructor #-}

```
