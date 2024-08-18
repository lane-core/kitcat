Lane Biocini
March 27st, 2024

```agda
{-# OPTIONS --safe #-}

module Prim.Bool where

open import Prim.Universe

data Bool : Type where
 ₀ : Bool
 ₁ : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE ₁ #-}
{-# BUILTIN FALSE ₀ #-}
