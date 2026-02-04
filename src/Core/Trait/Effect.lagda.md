Effect: universe-polymorphic type constructors for functor/monad hierarchies.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Effect where

open import Core.Type

```

An `Effect` packages a type constructor with its universe adjustment function.
Most effects (List, Maybe, State, etc.) preserve universe levels, but some
(like power sets) need to bump the level. The `adj` field handles this
uniformly.

This follows 1lab's `Meta.Idiom.Effect` pattern, enabling universe-polymorphic
Functor, Applicative, Monad, and Alternative hierarchies.

```agda

record Effect : Typeω where
  constructor impl
  field
    {adj} : Level → Level
    ₀     : ∀ {ℓ} → Type ℓ → Type (adj ℓ)

Impl
  : {ℓ : Level → Level}
  → (∀ {u} → Type u → Type (ℓ u))
  → (Effect → Typeω)
  → Typeω
Impl F T = T (impl F)


```

