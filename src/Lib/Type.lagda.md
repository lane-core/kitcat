```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Type where

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
