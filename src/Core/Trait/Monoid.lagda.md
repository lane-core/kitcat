Monoid trait: semigroup with an identity element.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Monoid where

open import Core.Type
open import Core.Base using (_≡_; refl)
open import Core.Trait.Semigroup public

private variable
  u : Level
  A : Type u

```

## Monoid Trait

A monoid extends a semigroup with an identity element and its laws. The `@0`
annotation makes the identity laws erased at runtime, while still requiring
them when constructing instances. Uses noun-adjective naming: `meqvl` for
left identity (`mempty <> x ≡ x`) and `meqvr` for right identity.

```agda

record Monoid {u} (A : Type u) : Type u where
  no-eta-equality
  field
    ⦃ Semigroup-Monoid ⦄ : Semigroup A
    mempty : A
    @0 meqvl : (x : A) → mempty <> x ≡ x
    @0 meqvr : (x : A) → x <> mempty ≡ x

open Monoid ⦃ ... ⦄ public hiding (Semigroup-Monoid)
{-# INLINE Monoid.constructor #-}

```
