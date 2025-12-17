```agda

{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}

module Lib.Core.Glue where

open import Lib.Core.Prim using (Type; Level)
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Core.HCompU
open import Lib.Core.Equiv

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

