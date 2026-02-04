Traversable trait: types that can be traversed with an applicative effect.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Traversable where

open import Core.Type
open import Core.Trait.Effect
open import Core.Trait.Map
open import Core.Trait.Applicative
open import Core.Trait.Foldable

```

A traversable functor extends both Functor and Foldable with the ability to
traverse a structure while collecting applicative effects. The `traverse`
operation maps each element to an effectful computation, then sequences all
the effects while preserving the structure.

This follows the Haskell/Idris Traversable pattern, enabling generic effectful
traversal of container types.

```agda

record Traversable (F : Effect) : Typeω where
  no-eta-equality
  private module F = Effect F
  field
    ⦃ Map-Traversable ⦄ : Map F
    ⦃ Foldable-Traversable ⦄ : Foldable F
    traverse
      : ∀ {M : Effect} ⦃ _ : Applicative M ⦄
          {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      → (A → Effect.₀ M B) → F.₀ A → Effect.₀ M (F.₀ B)

open Traversable public
{-# INLINE Traversable.constructor #-}

```

Standard traversable operations derived from `traverse`.

```agda

module _ {F : Effect} ⦃ trav : Traversable F ⦄ where
  private module F = Effect F

  sequence
    : ∀ {M : Effect} ⦃ _ : Applicative M ⦄
        {ℓ} {A : Type ℓ}
    → F.₀ (Effect.₀ M A) → Effect.₀ M (F.₀ A)
  sequence = traverse trav id

  for
    : ∀ {M : Effect} ⦃ _ : Applicative M ⦄
        {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → F.₀ A → (A → Effect.₀ M B) → Effect.₀ M (F.₀ B)
  for fa f = traverse trav f fa

```
