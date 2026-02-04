Partial elements and extension types.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Sub where

open import Core.Type
open import Core.Base

private module S where
  open import Agda.Builtin.Cubical.Sub public
open S renaming (primSubOut to outS; Sub to _[_↦_]) public


partial-pushout
  : ∀ {ℓ} (i j : I) {A : Partial (i ∨ j) (Type ℓ)}
    {ai : PartialP {a = ℓ} (i ∧ j) (λ { (j ∧ i = i1) → A 1=1 }) }
  → (.(z : IsOne i)
    → A (is1-left i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → (.(z : IsOne j)
    → A (is1-right i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → PartialP (i ∨ j) A
partial-pushout i j u v = primPOr i j (λ z → outS (u z)) (λ z → outS (v z))
