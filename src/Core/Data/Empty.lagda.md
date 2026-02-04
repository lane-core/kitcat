```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Core.Data.Empty where

open import Core.Type

module Void where
  data ⊥ : Type where

  ind : ∀ {u} (@0 P : ⊥ → Type u) (@0 e : ⊥) → P e
  ind P ()

  Void : ∀ {u} → Type u
  Void {u} = Lift u ⊥

open Void using (⊥) public

infixl 5 ¬_

ex-falso : ∀ {u} {@0 A : Type u} → (@0 e : ⊥) → A
ex-falso {A = A} = Void.ind (λ _ → A)

¬_ : ∀ {u} → Type u → Type u
¬ A = A → ⊥

Not = ¬_
{-# DISPLAY Not A = ¬ A #-}

¬¬_ : ∀ {u} → Type u → Type u
¬¬_ A = ¬ (¬ A)

```