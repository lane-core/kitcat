Decidable types.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Dec.Type where

open import Core.Type
open import Core.Data.Empty
open import Core.Data.Sigma.Type

open import Agda.Builtin.Cubical.Path using (_≡_)

data Dec {u} (A : Type u) : Type u where
  yes : A → Dec A
  no : ¬ A → Dec A

DecEq : ∀ {u} → Type u → Type u
DecEq A = (x y : A) → Dec (x ≡ y)

is-stable : ∀ {u} → Type u → Type u
is-stable A = ¬ (¬ A) → A

is-collapsible : ∀ {u} → Type u → Type u
is-collapsible A = Σ λ (f : A → A) → ∀ (x y : A) → f x ≡ f y

```
