```agda
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Cubical.Sub where

open import Lib.Type
open import Lib.Cubical.Base
open import Lib.Sigma
open import Lib.Cubical.Kan
open import Lib.Path

private module X where
  open import Agda.Builtin.Cubical.Sub public
open X renaming (primSubOut to outS; Sub to _[_↦_]) public

partial-pushout
  : ∀ {ℓ} (i j : I) {A : Partial (i ∨ j) (Type ℓ)}
    {ai : PartialP {a = ℓ} (i ∧ j) (λ { (j ∧ i = i1) → A 1=1 }) }
  → (.(z : IsOne i) → A (is1-left  i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → (.(z : IsOne j) → A (is1-right i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → PartialP (i ∨ j) A
partial-pushout i j u v = primPOr i j (λ z → outS (u z)) (λ z → outS (v z))
