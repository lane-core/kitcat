```agda

{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}

module Prim.Glue where

open import Prim.Type using (Type; Level)
open import Prim.Data.Sigma
open import Prim.Interval
open import Prim.HCompU
open import Prim.Equiv

private primitive
  primGlue    : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
    → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
    → Type ℓ'
  prim^glue   : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → PartialP φ T → A → primGlue A T e
  prim^unglue : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → primGlue A T e → A

private variable ℓ ℓ' : Level

Glue : (A : Type ℓ) {φ : I}
     → (Te : Partial φ (Σ T ∶ Type ℓ' , T ≃ A)) → Type ℓ'
Glue A {φ} Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

