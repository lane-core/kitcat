```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Data.Sigma where

open import Prim.Type
--open import Meta.Underlying public
--open import Meta.Cartesian public
--open import Meta.Operator public

--infixr -1 Σ-syntax

```

Import the Sigma type from Agda.Builtin. We'll use TypeTopology's
notation because its far more convenient. We can use textbook style
notation if we want to annotate the type name with a syntax
declaration.

```
open import Agda.Builtin.Sigma public
  renaming ( Σ to Sigma
           ; _,_ to infixr 4 _,_ )
  using ( fst; snd; module Σ ) -- keep the module the same name, it works

Σ : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ {A = A} B = Sigma A B
{-# INLINE Σ #-}
{-# INLINE _,_ #-}

{-# DISPLAY Sigma _ B = Σ B #-}

_×_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
_×_ A B = Sigma A (λ _ → B)

-- Σ-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄
--          → (X : A) (F : ⌞ X ⌟ → Type ℓ') → Type _
-- Σ-syntax X F = Sigma ⌞ X ⌟ F
-- syntax Σ-syntax A (λ x → M) = Σ x ∶ A , M
-- {-# DISPLAY Σ-syntax _ B = Σ B #-}

-- instance
  -- Cartesian-Σ : ∀ {u v} {A : Type u} {B : Type v}
  --             → Cartesian (λ A B → Sigma {u} {v} A λ _ → B)
  -- Cartesian-Σ .Cartesian.cons = {!!}
  -- Cartesian-Σ .Cartesian.pr1 = {!!}
  -- Cartesian-Σ .Cartesian.pr2 = {!!}
  -- Cartesian-Σ .Cartesian.ind = {!!}

  -- Times-Σ : ∀ {u v} → Times λ (A : Type u) (B : Type v) → Type (u ⊔ v)
  -- Times-Σ .Times._×_ A B = Σ _ ∶ A , B

  -- Σ-instance : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  --            → ⦃ x : A ⦄ ⦃ y : B x ⦄ → Σ B
  -- Σ-instance ⦃ x ⦄ .fst = x
  -- Σ-instance ⦃ y ⦄ .snd = y

  -- Underlying-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  --              → ⦃ ua : Underlying A ⦄
  --              → Underlying (Σ B)
  -- Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  -- Underlying-Σ .⌞_⌟ x = ⌞ x .fst ⌟

diag : ∀ {ℓ} {A : Type ℓ} → A → A × A
diag a = a , a

swap : ∀ {u v} {A : Type u} {B : Type v} → A × B → B × A
swap (a , b) = b , a
