Operations on dependent pairs.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Sigma.Base where

open import Core.Type
open import Core.Data.Sigma.Type

dup : ∀ {u} {@0 A : Type u} → A → A × A
dup a = a , a
{-# INLINE dup #-}

swap : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A × B → B × A
swap (a , b) = b , a
{-# INLINE swap #-}

tot
  : ∀ {u v w} {A : Type u} {B : A → Type v} {C : A → Type w}
  → (∀ x → B x → C x) → Sigma A B → Sigma A C
tot f (a , b) = a , f a b
{-# INLINE tot #-}

```
