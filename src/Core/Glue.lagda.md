Glue types for constructing equivalences and univalence.

```agda

{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}

module Core.Glue where

open import Core.Type using (Type; Level)
open import Core.Base
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Sub using (_[_↦_]; outS; inS)
open import Core.HCompU
open import Core.Equiv using (_≃_; equiv)

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

-- Glue elimination: extract the base element from a Glue element
unglue : {A : Type ℓ} (φ : I) {Te : Partial φ (Σ T ∶ Type ℓ' , T ≃ A)}
       → Glue A Te → A
unglue φ {Te} = prim^unglue {e = λ o → Te o .snd}

glue : {A : Type ℓ} {φ : I} {Te : Partial φ (Σ T ∶ Type ℓ' , T ≃ A)}
     → (t : PartialP φ (λ o → Te o .fst))
     → (a : A [ φ ↦ (λ o → Te o .snd .fst (t o)) ])
     → Glue A Te
glue {Te = Te} t a = prim^glue {e = λ o → Te o .snd} t (outS a)

