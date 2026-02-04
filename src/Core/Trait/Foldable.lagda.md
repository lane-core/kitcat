Foldable trait: types that can be folded to a summary value.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Foldable where

open import Core.Type using (Level; Type; Typeω; _⊔_)
open import Core.Data.Bool using (Bool; false; true)
open import Core.Data.Nat.Type
open import Core.Trait.Effect
open import Core.Trait.Semigroup
open import Core.Trait.Monoid

```

A foldable bundles a type constructor with a fold operation. The `foldr`
operation is the fundamental method: it processes elements right-to-left,
building a result from an initial value and a combining function.

This follows the Haskell/Idris Foldable pattern, enabling generic traversal
of container types.

```agda

record Foldable (F : Effect) : Typeω where
  no-eta-equality
  private module F = Effect F
  field
    foldr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B → B) → B → F.₀ A → B

open Foldable public
{-# INLINE Foldable.constructor #-}

```

Standard foldable operations derived from `foldr`.

```agda

module _ {F : Effect} ⦃ fold : Foldable F ⦄ where
  private module F = Effect F

  foldl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (B → A → B) → B → F.₀ A → B
  foldl {B = B} f z t = foldr fold {B = B → B} (λ a g b → g (f b a)) (λ b → b) t z

  foldr' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B → B) → B → F.₀ A → B
  foldr' = foldr fold

  length : ∀ {ℓ} {A : Type ℓ} → F.₀ A → Nat
  length = foldr fold (λ _ n → S n) Z

  null : ∀ {ℓ} {A : Type ℓ} → F.₀ A → Bool
  null = foldr fold (λ _ _ → false) true

```

The `foldMap` operation requires a Monoid constraint on the target type.
It maps each element to a monoid value and combines them.

```agda

  foldMap
    : ∀ {ℓ ℓ'} {A : Type ℓ} {M : Type ℓ'}
    → ⦃ mon : Monoid M ⦄
    → (A → M) → F.₀ A → M
  foldMap ⦃ mon ⦄ f = foldr fold (λ a m → f a <> m) mempty
    where instance _ = Monoid.Semigroup-Monoid mon

```
