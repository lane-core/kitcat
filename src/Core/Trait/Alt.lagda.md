Choice/alternation trait for type constructors.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Alt where

open import Core.Type

```

## Alt Trait

Choice/alternation from Haskell's `Alternative`, without requiring `Applicative`.

```agda

record Alt {u v} (F : Type u → Type v) : Typeω where
  no-eta-equality
  infixl 3 _<|>_
  field
    _<|>_ : ∀ {A} → F A → F A → F A

open Alt ⦃ ... ⦄ public
{-# INLINE Alt.constructor #-}

```
