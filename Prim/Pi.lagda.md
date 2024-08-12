Lane Biocini
July 9th, 2024
revised August 1st, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Pi where

infix -1 Pi ev-syntax

open import Prim.Universe

open import Control.Composition public
open import Control.Underlying public

syntax Pi A (λ x → b) = Π x ꞉ A , b
Pi : ∀ {𝓊 𝓋} (A : 𝓊 type) (B : A → 𝓋 type) → 𝓊 ⊔ 𝓋 type
Pi A B = (x : A) → B x

Π : ∀ {𝓊 𝓋} {A : 𝓊 type} (B : A → 𝓋 type) → 𝓊 ⊔ 𝓋 type
Π B = Pi _ B
{-# DISPLAY Pi A B = Π B #-}

syntax ev-syntax (λ x → b) = x ↦ b
ev-syntax : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : A → 𝓋 type}
           → Π B → Π B
ev-syntax = λ x → x
{-# INLINE ev-syntax #-}

id : ∀ {𝓊} {A : 𝓊 type} → A → A
id = λ x → x
{-# INLINE id #-}

const : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type}
      → A → B → A
const x = λ _ → x
{-# INLINE const #-}

Const : ∀ 𝓊 {𝓋} → 𝓋 ⁺ type → 𝓊 ⁺ type
Const 𝓊 = const (𝓊 type)
{-# INLINE Const #-}

swap : ∀ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : A → B → 𝓌 type}
     → ((x : A) → Π (C x))
     → ((y : B) → Π (λ x → C x y))
swap f = λ y x → f x y
{-# INLINE swap #-}

dom : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : A → 𝓋 type} → Π B → 𝓊 type
dom {𝓊} {𝓋} {A} = const A

cod : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} → (A → B) → 𝓋 type
cod {𝓊} {𝓋} {A} {B} = const B

ev : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : A → 𝓋 type}
   → Π B → (x : A) → B x
ev f = f
{-# INLINE ev #-}

S : ∀ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : A → 𝓋 type} {C : (x : A) → B x → 𝓌 type}
  → (Π x ꞉ A , Π y ꞉ B x , C x y)
  → (f : Pi A B) (x : A) → C x (f x)
S g f = λ x → g x (f x)
{-# INLINE S #-}

instance
 underlying-Π : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : A → 𝓋 type}
              → {x : A} → Underlying (Π B)
 underlying-Π {𝓊} .Underlying.ℓ = 𝓊
 underlying-Π {𝓊} {𝓋} {A} .⌞_⌟ p = A
