Pullbacks: fiber products and their universal property.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Function.Pullback where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Equiv
open import Core.Kan

Pullback
  : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
  → (f : A → C) (g : B → C) → Type (u ⊔ v ⊔ w)
Pullback {A = A} {B = B} f g = Σ (a , b) ∶ A × B , f a ≡ g b

module Pullback where

  private variable
    u v w : Level

  module _ {A : Type u} {B : Type v} {C : Type w}
    {f : A → C} {g : B → C} where

    inl : Pullback f g → A
    inl ((a , _) , _) = a
    {-# INLINE inl #-}

    inr : Pullback f g → B
    inr ((_ , b) , _) = b
    {-# INLINE inr #-}

    comm
      : (p : Pullback f g) → f (inl p) ≡ g (inr p)
    comm (_ , c) = c
    {-# INLINE comm #-}

    univ
      : ∀ {ℓ} {X : Type ℓ}
      → (h : X → A) (k : X → B)
      → ((x : X) → f (h x) ≡ g (k x))
      → X → Pullback f g
    univ h k c x = (h x , k x) , c x

```


## Fiber as pullback

A fiber of `f` at `b` is the pullback of `f` with the constant
map at `b`.

```agda

  fiber≃pullback
    : ∀ {A : Type u} {B : Type v} {f : A → B} {b : B}
    → fiber f b ≃ Pullback f (λ (_ : ⊤) → b)
  fiber≃pullback {f = f} {b = b} =
    iso→equiv fwd bwd (λ _ → refl) retr
    where
    fwd : fiber f b → Pullback f (λ _ → b)
    fwd (a , p) = (a , tt) , p

    bwd : Pullback f (λ _ → b) → fiber f b
    bwd ((a , _) , p) = a , p

    retr
      : (y : Pullback f (λ _ → b))
      → fwd (bwd y) ≡ y
    retr ((a , tt) , p) = refl

```


## Swap

The pullback is symmetric: `Pullback f g ≃ Pullback g f`.

```agda

  swap
    : ∀ {A : Type u} {B : Type v} {C : Type w}
    → {f : A → C} {g : B → C}
    → Pullback f g ≃ Pullback g f
  swap = iso→equiv
    (λ { ((a , b) , p) → (b , a) , sym p })
    (λ { ((b , a) , p) → (a , b) , sym p })
    (λ _ → refl)
    (λ _ → refl)

```
