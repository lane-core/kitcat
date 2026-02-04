Group trait: monoid with inverses.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Group where

open import Core.Type
open import Core.Base using (_≡_; refl)
open import Core.Trait.Monoid public

private variable
  u : Level
  A : Type u

```

## Group Trait

A group extends a monoid with an inverse operation and its laws. The `@0`
annotation makes the inverse laws erased at runtime, while still requiring
them when constructing instances. Uses noun-adjective naming: `ginvl` for
left inverse (`ginv x <> x ≡ mempty`) and `ginvr` for right inverse
(`x <> ginv x ≡ mempty`).

```agda

record Group {u} (A : Type u) : Type u where
  no-eta-equality
  field
    ⦃ Monoid-Group ⦄ : Monoid A

  private
    module M = Monoid Monoid-Group
    module S = Semigroup M.Semigroup-Monoid

  field
    ginv : A → A
    @0 ginvl : (x : A) → S._<>_ (ginv x) x ≡ M.mempty
    @0 ginvr : (x : A) → S._<>_ x (ginv x) ≡ M.mempty

open Group ⦃ ... ⦄ public hiding (Monoid-Group)
{-# INLINE Group.constructor #-}

```
