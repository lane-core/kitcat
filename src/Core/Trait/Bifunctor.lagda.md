Bifunctor trait: type constructors with two covariant type parameters.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Bifunctor where

open import Core.Type
open import Core.Base using (_≡_; refl; _~_)
open import Core.Data.Sigma using (_×_; _,_; fst; snd)
open import Core.Data.Sum using (_⊎_; inl; inr)

private variable
  u v : Level
  A B C D : Type u

```

A bifunctor is a type constructor `F : Type -> Type -> Type` with a mapping
operation `bimap` that is functorial in both arguments. The laws require that
`bimap id id` is the identity and that `bimap` respects composition.

```agda

record Bifunctor {ℓ₁ ℓ₂ ℓ₃} (F : Type ℓ₁ → Type ℓ₂ → Type ℓ₃) : Typeω where
  no-eta-equality
  field
    bimap : ∀ {A C : Type ℓ₁} {B D : Type ℓ₂}
          → (A → C) → (B → D) → F A B → F C D
    @0 bimap-id : ∀ {A : Type ℓ₁} {B : Type ℓ₂}
                → bimap {A} {A} {B} {B} id id ~ id
    @0 bimap-∘ : ∀ {A C E : Type ℓ₁} {B D G : Type ℓ₂}
               → (f : A → C) (g : C → E) (h : B → D) (k : D → G)
               → bimap (g ∘ f) (k ∘ h) ~ bimap g k ∘ bimap f h

open Bifunctor ⦃ ... ⦄ public
{-# INLINE Bifunctor.constructor #-}

```

Map over only the first or second component.

```agda

mapFst
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {F : Type ℓ₁ → Type ℓ₂ → Type ℓ₃}
  → ⦃ Bifunctor F ⦄
  → {A C : Type ℓ₁} {B : Type ℓ₂}
  → (A → C) → F A B → F C B
mapFst f = bimap f id

mapSnd
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {F : Type ℓ₁ → Type ℓ₂ → Type ℓ₃}
  → ⦃ Bifunctor F ⦄
  → {A : Type ℓ₁} {B D : Type ℓ₂}
  → (B → D) → F A B → F A D
mapSnd g = bimap id g

```

```agda

instance
  Bifunctor-× : ∀ {ℓ₁ ℓ₂} → Bifunctor {ℓ₁} {ℓ₂} {ℓ₁ ⊔ ℓ₂} _×_
  Bifunctor-× .Bifunctor.bimap f g (a , b) = f a , g b
  Bifunctor-× .Bifunctor.bimap-id _ = refl
  Bifunctor-× .Bifunctor.bimap-∘ _ _ _ _ _ = refl

```

```agda

instance
  Bifunctor-⊎ : ∀ {ℓ₁ ℓ₂} → Bifunctor {ℓ₁} {ℓ₂} {ℓ₁ ⊔ ℓ₂} _⊎_
  Bifunctor-⊎ .Bifunctor.bimap f g (inl a) = inl (f a)
  Bifunctor-⊎ .Bifunctor.bimap f g (inr b) = inr (g b)
  Bifunctor-⊎ .Bifunctor.bimap-id (inl _) = refl
  Bifunctor-⊎ .Bifunctor.bimap-id (inr _) = refl
  Bifunctor-⊎ .Bifunctor.bimap-∘ _ _ _ _ (inl _) = refl
  Bifunctor-⊎ .Bifunctor.bimap-∘ _ _ _ _ (inr _) = refl

```
