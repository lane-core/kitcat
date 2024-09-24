Lane Biocini
revised August 25th, 2024

```agda

{-# OPTIONS --safe #-}

module Lib.Sigma where

infix -1 Sigma
infix 3 Σ
infixr 4 _,_
infixr 5 _×_

open import Lib.Prim

record Σ {𝓊 𝓋} {A : 𝓊 type} (B : A → 𝓋 type) : 𝓊 ⊔ 𝓋 type where
 constructor _,_
 field
  fst : A
  snd : B fst

open Σ public

Sigma : ∀ {𝓊 𝓋} (A : 𝓊 type) → (A → 𝓋 type) → 𝓊 ⊔ 𝓋 type
Sigma {𝓊} {𝓋} A B = Σ {𝓊} {𝓋} {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

{-# DISPLAY Sigma A B = Σ B #-}
{-# BUILTIN SIGMA Sigma #-}

_×_ Pair : ∀ {𝓊 𝓋} → 𝓊 type → 𝓋 type → 𝓊 ⊔ 𝓋 type
_×_ A B = Sigma A (λ _ → B)
Pair = _×_

ind : ∀ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : A → 𝓋 type}
  → (P : Σ x ꞉ A , B x → 𝓌 type)
  → ((x : A) (y : B x) → P (x , y))
  → (s : Σ x ꞉ A , B x)
  → P s
ind P b s = b (s .fst) (s .snd)

functor : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : A → 𝓋 type}
      → (f : A → A) (g : (x : A) → B x → B (f x))
      → Σ x ꞉ A , B x
      → Σ x ꞉ A , B (f x)
functor f g p = p .fst , g (p .fst) (p .snd)

ev : ∀ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : A → 𝓋 type}
 → (P : Σ x ꞉ A , B x → 𝓌 type)
 → ((z : Σ x ꞉ A , B x) → P z)
 → (x : A) (y : B x) → P (x , y)
ev P s = λ x y → s (x , y)
