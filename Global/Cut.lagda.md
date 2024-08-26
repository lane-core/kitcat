Lane Fiocini
Jun 30, 2024

Combinators for reasoning. Notice that we can define composition,
identity, and reasoning chains with the same record.

```
{-# OPTIONS --safe #-}

module Global.Cut where

open import Prim.Universe

module _ {𝓊 𝓋 𝓌} where
 record Cut (X : 𝓊 type)
            (A : X → 𝓋 type)
            (B : ∀ {x} → A x → 𝓌 type) : 𝓤ω where
  infixr 40 seq _∙_ _∘_
  infixr 2 cut-syntax

  field
   seq : ∀ {x} (a : A x) → B a
  {-# INLINE seq #-}

  _∙_ : ∀ {x} (a : A x) → B a
  _∙_ = seq
  {-# INLINE _∙_ #-}

  syntax cut-syntax x a b = x ⊢ a , b
  _∘_ cut-syntax : ∀ x → (a : A x) → B a
  _∘_ x = seq {x}
  cut-syntax x = seq {x}
  {-# INLINE _∘_ #-}
  {-# INLINE cut-syntax #-}

 open Cut ⦃ ... ⦄ public

{-# DISPLAY Cut.seq _ = _∙_ #-}
{-# DISPLAY Cut._∙_ _ = _∙_ #-}
{-# DISPLAY Cut._∘_ _ = _∘_ #-}

module _ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : B → 𝓌 type} where
 instance
  reasoning-Π : Cut (∀ y → C y) (λ g → A → B) (λ f → (x : A) → C (f x))
  reasoning-Π .seq {g} f = λ x → g (f x)
  {-# INLINE reasoning-Π #-}
