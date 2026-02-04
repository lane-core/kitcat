Decidable propositions and decision combinators.

This module provides the `Decidable` trait and combinators for working with
`Dec` values in a composable way.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Decidable where

open import Core.Type
open import Core.Base
open import Core.Data.Bool
open import Core.Data.Dec public
open import Core.Data.Sum
open import Core.Data.Empty
open import Core.Data.Sigma
open import Core.Trait.Alt

private variable
  u v : Level
  A B : Type u

```

## Decidable Trait

```agda

record Decidable {u} (A : Type u) : Type u where
  no-eta-equality
  field
    decide : Dec A

open Decidable ⦃ ... ⦄ public
{-# INLINE Decidable.constructor #-}

```

## Dec Eliminators

```agda

dec : ∀ {u v} {A : Type u} {B : Type v}
    → (A → B) → (¬ A → B) → Dec A → B
dec f g (yes a) = f a
dec f g (no ¬a) = g ¬a

dec-map : ∀ {A : Type u} {B : Type v}
        → (A → B) → (B → A) → Dec A → Dec B
dec-map f g (yes a) = yes (f a)
dec-map f g (no ¬a) = no (λ b → ¬a (g b))

```

## Reflects

Connects `Dec` to `Bool` for proof by reflection.

```agda

data Reflects {u} (A : Type u) : Bool → Type u where
  ofʸ : A   → Reflects A true
  ofⁿ : ¬ A → Reflects A false

invert : ∀ {b} → Reflects A b → Bool.if-then-else b A (¬ A)
invert (ofʸ a)  = a
invert (ofⁿ ¬a) = ¬a

```

## Dec Combinators

```agda

infixr 6 _∧ᵈ_
infixr 5 _∨ᵈ_
infix 8 ¬ᵈ_

-- Conjunction of decisions
_∧ᵈ_ : Dec A → Dec B → Dec (A × B)
yes a ∧ᵈ yes b = yes (a , b)
yes a ∧ᵈ no ¬b = no (λ { (_ , b) → ¬b b })
no ¬a ∧ᵈ _     = no (λ { (a , _) → ¬a a })

-- Disjunction of decisions
_∨ᵈ_ : Dec A → Dec B → Dec (A ⊎ B)
yes a ∨ᵈ _     = yes (inl a)
no _  ∨ᵈ yes b = yes (inr b)
no ¬a ∨ᵈ no ¬b = no λ { (inl a) → ¬a a ; (inr b) → ¬b b }

-- Negation of decision
¬ᵈ_ : Dec A → Dec (¬ A)
¬ᵈ yes a = no (λ ¬a → ¬a a)
¬ᵈ no ¬a = yes ¬a

```

## Alt Instance

```agda

instance
  Alt-Dec : ∀ {u} → Alt (Dec {u})
  Alt-Dec ._<|>_ (yes a) _ = yes a
  Alt-Dec ._<|>_ (no _)  d = d

```

## Decidable Instances

```agda

instance
  Decidable-⊤ : Decidable ⊤
  Decidable-⊤ .decide = yes tt

  Decidable-⊥ : Decidable ⊥
  Decidable-⊥ .decide = no (λ x → x)

```
