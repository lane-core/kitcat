Dependent pairs and products.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Sigma.Type where

open import Core.Type

open import Agda.Builtin.Sigma public
  renaming ( Σ to Sigma
           ; _,_ to infixr 4 _,_ )
  using (fst; snd; module Σ)

Σ : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ {A = A} B = Sigma A B
{-# INLINE Σ #-}
{-# INLINE _,_ #-}
{-# DISPLAY Sigma _ B = Σ B #-}

infixr 4 _×_
_×_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
_×_ A B = Sigma A (λ _ → B)

Σ-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄
         → (X : A) (F : ⌞ X ⌟ → Type ℓ') → Type _
Σ-syntax X F = Sigma ⌞ X ⌟ F
infixr -1 Σ-syntax
syntax Σ-syntax A (λ x → M) = Σ x ∶ A , M
{-# DISPLAY Σ-syntax _ B = Σ B #-}

instance
  Underlying-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
               → ⦃ ua : Underlying A ⦄
               → Underlying (Σ B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟ x = ⌞ x .fst ⌟

```
