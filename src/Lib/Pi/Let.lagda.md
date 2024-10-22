Lane Biocini
Ulf Norell (code taken from agda-prelude)
Oct 12th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Pi.Let where

infixr 0 let-syntax

open import Lib.Prim

let-syntax : ∀ {u v} {A : u type} {B : v type} → A → (A → B) → B
let-syntax x f = f x
syntax let-syntax e (λ x → b) = let[ x := e ] b
