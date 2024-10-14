Lane Biocini
revised August 25th, 2024

```agda

{-# OPTIONS --safe #-}

module Lib.Data.Sigma where

open import Lib.Prim

infix 3 Σ
infix -1 Sigma
infixr 4 _,_

record Σ {u v} {A : u type} (B : A → v type) : u ⊔ v type where
 constructor _,_
 field
  fst : A
  snd : B fst

open Σ public

Sigma : ∀ {u v} (A : u type) → (A → v type) → u ⊔ v type
Sigma {u} {v} A B = Σ {u} {v} {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

{-# DISPLAY Sigma A B = Σ B #-}
{-# BUILTIN SIGMA Sigma #-}
