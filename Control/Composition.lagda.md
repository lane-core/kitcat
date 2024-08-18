Lane Fiocini
Jun 30, 2024

Combinators for reasoning. Notice that we can define composition,
identity, and reasoning chains with the same record.

```
{-# OPTIONS --safe #-}

module Control.Composition where

open import Prim.Universe
open import Control.Arrow

module _ {𝓊 𝓋 𝓌} where
 record Cut (X : 𝓊 type) (A : X → 𝓋 type) (B : ∀ {x} → A x → 𝓌 type) : 𝓤ω where
  infixr 40 seq _∙_ _∘_

  field
   seq : ∀ {x} (a : A x) → B a
  {-# INLINE seq #-}

  _∙_ : ∀ {x} (a : A x) → B a
  _∙_ = seq
  {-# INLINE _∙_ #-}

  _∘_ _,_⊢_ : ∀ x (a : A x) → B a
  _∘_ x = seq {x}
  _,_⊢_ x = seq {x}
  {-# INLINE _∘_ #-}
  {-# INLINE _,_⊢_ #-}

 open Cut ⦃ ... ⦄ public

{-# DISPLAY Cut.seq _ = _∙_ #-}
{-# DISPLAY Cut._∘_ _ = _∘_ #-}
{-# DISPLAY Cut._,_⊢_ _ = _,_⊢_ #-}


module _ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : 𝓌 type} where
 instance
  reasoning-λ : Cut (B → C) (λ g → A → B) (λ f → A → C)
  reasoning-λ .seq {g} f = λ x → g (f x)

module _ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : B → 𝓌 type} where
 instance
  reasoning-Π : Cut (∀ y → C y) (λ g → A → B) (λ f → (x : A) → C (f x))
  reasoning-Π .seq {g} f = λ x → g (f x)
