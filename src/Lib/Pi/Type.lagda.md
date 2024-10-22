Lane Biocini
Ulf Norell (code taken from agda-prelude)
Oct 12th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Pi.Type where

open import Lib.Prim

infix 3 Π
infix -1 NatT
infix -1 Pi

Π : ∀ {u v} {A : u type} (B : A → v type) → u ⊔ v type
Π {u} {v} {A} B = (x : A) → B x
{-# INLINE Π #-}

Pi : ∀ {u v} (A : u type) (B : A → v type) → u ⊔ v type
Pi A B = Π B
syntax Pi A (λ x → b) = Π x ꞉ A , b

NatT : ∀ {u v w} {ob : u type} → (ob → v type) → (ob → w type) → u ⊔ v ⊔ w type
NatT A B = ∀ x → A x → B x
syntax NatT A B = A ~> B
