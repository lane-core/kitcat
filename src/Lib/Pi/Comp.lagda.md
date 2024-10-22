Lane Biocini
Ulf Norell (code taken from agda-prelude)
Oct 12th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Pi.Comp where

infixr 9 comp
infixr 9 _∘′_
infixl 8 _on_

open import Lib.Prim
open import Lib.Pi.Type
open import Lib.Trait.Cut

comp : ∀ {u v w} {A : u type} {B : A → v type} {C : ∀ x → B x → w type}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
comp f g = λ x → f (g x)
{-# INLINE comp #-}

_∘′_ : ∀ {u v w} {A : u type} {B : v type} {C : w type} →
         (B → C) → (A → B) → (A → C)
f ∘′ g = comp f g
{-# INLINE _∘′_ #-}

_on_ : ∀ {u v w} {A : u type} {B : A → v type} {C : ∀ x y → B x → B y → w type} →
         (∀ {x y} (z : B x) (w : B y) → C x y z w) → (f : ∀ x → B x) → ∀ x y →
         C x y (f x) (f y)
h on f = λ x y → h (f x) (f y)
{-# INLINE _on_ #-}

module _ {u v w} {A : u type} {B : v type} {C : B → w type} where
 instance
  reasoning-Π : Cut (∀ y → C y) (λ g → A → B) (λ _ f → (x : A) → C (f x))
  reasoning-Π .seq {g} f = comp g f
  {-# INLINE reasoning-Π #-}
