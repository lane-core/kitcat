```agda

{-# OPTIONS --safe --erased-cubical #-}

module HData.Circle where

open import Lib.Core.Prim
open import Lib.Core.Base

open import Data.Bits

data Circle : Type where
  base : Circle
  loop : base ≡ base

Circle-rec : ∀ {ℓ} {A : Type ℓ} (b : A) (l : b ≡ b) → Circle → A
Circle-rec b l base = b
Circle-rec b l (loop i) = l i

Circle-elim : ∀ {ℓ} {A : Circle → Type ℓ} (b : A base) (l : PathP (λ i → A (loop i)) b b)
            → ∀ s → A s
Circle-elim b l base = b
Circle-elim b l (loop i) = l i

Circle-elim0 : ∀ {ℓ} {A : @0 Circle → Type ℓ} (b : A base) (l : PathP (λ i → A (loop i)) b b)
             → ∀ s → A s
Circle-elim0 b l base = b
Circle-elim0 b l (loop i) = l i
