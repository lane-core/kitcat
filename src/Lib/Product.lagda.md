Lane Biocini
Oct 20th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Product where

open import Lib.Prim

open import Lib.Data.Sigma public
open import Lib.Trait.Object using (is-pair-type; _×_; pr₁; pr₂) public

instance
 sg-product : ∀ {u v}
            → is-pair-type (λ (A : u type) (B : v type) → Σ _ ꞉ A , B)
 sg-product .pr₁ = fst
 sg-product .pr₂ = snd
