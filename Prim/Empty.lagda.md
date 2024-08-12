Lane Biocini
March 27st, 2024
revised August 3rd, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Empty where

infix 3 ¬_

open import Prim.Universe
open import Prim.Pi

data 𝟘 {𝓊} : 𝓊 type where

⊥ : Type
⊥ = 𝟘

ex-falso : ∀ {𝓊 𝓋} {A : 𝓋 type} → 𝟘 {𝓊} → A
ex-falso = λ ()

-- _≠_ : ∀ {𝓊} {A : 𝓊 type} → A → A → 𝓊 type
-- _≠_ x y = x ≡ y → ⊥

contrapositive : ∀ {𝓊 𝓋} {P : 𝓊 type} {Q : 𝓋 type}
      → (P → Q) → (Q → ⊥) → (P → ⊥)
contrapositive a nq p = nq (a p)

module Empty where
 ind : ∀ {𝓊 𝓋} (B : 𝟘 {𝓊} → 𝓋 type) → (e : 𝟘) → B e
 ind A = λ ()

module _ where
¬_ : ∀ {𝓊} → 𝓊 type → 𝓊 type
¬ A = A → ⊥

¬¬_ : ∀ {𝓊} → 𝓊 type → 𝓊 type
¬¬ A = ¬ (¬ A)

¬¬¬_ : ∀ {𝓊} → 𝓊 type → 𝓊 type
¬¬¬ A = ¬ (¬ A)

record Uninhabited {𝓊} (A : 𝓊 type) : 𝓊 type where
 field
  void : A → ⊥

 -- elim : ∀ {𝓋} {B : 𝓋 type} → A → B
 -- elim x = {!!}

open Uninhabited ⦃ ... ⦄ public

module _ {𝓊} {A : 𝓊 type} where
 instance
  null : {{¬ A}} → Uninhabited A
  null {{na}} .void = na
