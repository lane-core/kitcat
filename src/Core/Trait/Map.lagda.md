Map trait: types with a structure-preserving map operation.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Map where

open import Core.Type
open import Core.Base using (_≡_)
open import Core.Trait.Effect

```

A functor bundles a type constructor with a map operation satisfying identity
and composition laws. The laws are erased (`@0`) since they are only needed
for type-checking proofs, not runtime computation.

This follows the 1lab `Meta.Idiom.Map` pattern, enabling universe-polymorphic
functors via the `Effect` abstraction.

```agda

record Map (M : Effect) : Typeω where
  no-eta-equality
  private module M = Effect M
  field
    map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → M.₀ A → M.₀ B
    @0 map-id : ∀ {ℓ} {A : Type ℓ} → map {A = A} id ≡ id
    @0 map-comp
      : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
      → {f : B → C} {g : A → B} → map (f ∘ g) ≡ map f ∘ map g

open Map public
{-# INLINE Map.constructor #-}

```

Standard functor operators following Haskell/Idris conventions.

```agda

module _ {M : Effect} ⦃ fun : Map M ⦄ where
  private module M = Effect M

  infixl 4 _<$>_ _<&>_ _<$_

  _<$>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → M.₀ A → M.₀ B
  _<$>_ = map fun

  _<&>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → (A → B) → M.₀ B
  ma <&> f = map fun f ma

  _<$_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → B → M.₀ A → M.₀ B
  b <$ ma = map fun (const b) ma

```
