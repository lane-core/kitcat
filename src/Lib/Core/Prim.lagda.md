```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Core.Prim where

open import Agda.Primitive public
  using ( SSet
        ; SSetω
        ; LevelUniv
        ; Level )
  renaming ( Set   to Type
           ; Setω  to Typeω
           ; _⊔_ to infixl 6 _⊔_
           ; lsuc to infixr 7 _₊
           ; lzero to 0ℓ )

1ℓ : Level
1ℓ = 0ℓ ₊

record Lift {u} a (A : Type u) : Type (u ⊔ a) where
  constructor lift
  field
    lower : A

open Lift public

level-of : ∀ {ℓ} {A : Type ℓ} → A → Level
level-of {ℓ} _ = ℓ

Type₊ : ∀ ℓ → Type (ℓ ₊ ₊)
Type₊ ℓ = Type (ℓ ₊)

𝓤 : Typeω
𝓤 = (u : Level) → Type u

record Underlying {ℓ} (A : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟   : A → Type ℓ-underlying

open Underlying ⦃ ... ⦄ public
{-# DISPLAY Underlying.⌞_⌟ _ X = ⌞ X ⌟ #-}

instance
  Underlying-Type : ∀ {ℓ} → Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟  = λ x → x

  Underlying-Lift : ∀ {ℓ ℓ'} {A : Type ℓ}
                  → ⦃ ua : Underlying A ⦄
                  → Underlying (Lift ℓ' A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟ x = ⌞ x .lower ⌟
