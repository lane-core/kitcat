Lane Biocini
August 1st, 2024

```agda

{-# OPTIONS --safe #-}

module Control.Translate where

open import Prim.Universe

record Translate {𝓊 𝓋} (A : 𝓊 type) (B : 𝓋 type) : 𝓤ω where
 field
  from : A → B

open Translate ⦃ ... ⦄ public
