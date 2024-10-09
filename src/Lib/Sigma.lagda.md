Lane Biocini
revised August 25th, 2024

```agda

{-# OPTIONS --safe #-}

module Lib.Sigma where

open import Lib.Prim

sg-ind : ∀ {u v w} {A : u type} {B : A → v type}
  → (P : Σ x ꞉ A , B x → w type)
  → ((x : A) (y : B x) → P (x , y))
  → (s : Σ x ꞉ A , B x)
  → P s
sg-ind P b s = b (s .fst) (s .snd)

sg-functor : ∀ {u v} {A : u type} {B : A → v type}
      → (f : A → A) (g : (x : A) → B x → B (f x))
      → Σ x ꞉ A , B x
      → Σ x ꞉ A , B (f x)
sg-functor f g p = p .fst , g (p .fst) (p .snd)

sg-ev : ∀ {u v w} {A : u type} {B : A → v type}
 → (P : Σ x ꞉ A , B x → w type)
 → ((z : Σ x ꞉ A , B x) → P z)
 → (x : A) (y : B x) → P (x , y)
sg-ev P s = λ x y → s (x , y)
