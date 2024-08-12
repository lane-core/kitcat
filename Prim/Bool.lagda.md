Lane Biocini
March 27st, 2024

```agda
{-# OPTIONS --safe #-}

module Prim.Bool where

open import Prim.Universe

data Bool : Type where
 ff : Bool
 tt : Bool

bool-induction : ∀ {𝓊} (P : Bool → 𝓊 type)
               → P ff → P tt
               → (b : Bool) → P b
bool-induction P f t ff = f
bool-induction P f t tt = t

!_ : Bool → Bool
!_ = bool-induction (λ _ → Bool) tt ff

_and_ : Bool → Bool → Bool
_and_ = bool-induction (λ _ → Bool → Bool) (λ _ → ff) (λ - → -)

_or_ : Bool → Bool → Bool
_or_ = bool-induction (λ _ → Bool → Bool) (λ - → -) (λ _ → tt)

if_then_else : ∀ {𝓊} {A : 𝓊 type} → Bool → A → A → A
if_then_else {𝓊} {A} = bool-induction (λ _ → A → A → A) (λ x y → y) (λ x y → x)
