Lane Biocini
August 26th, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Bool where

open import Prim.Universe

data Bool : Type where
 tt ff : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}

ind : ∀ {𝓊} (P : Bool → 𝓊 type) → P tt → P ff → (b : Bool) → P b
ind P t f tt = t
ind P t f ff = f

not : Bool → Bool
not = ind (λ _ → Bool) ff tt

or : Bool → Bool → Bool
or p = ind (λ _ → Bool) tt p

and : Bool → Bool → Bool
and p = ind (λ _ → Bool) p ff

record Eq {𝓊} (A : 𝓊 type) : 𝓊 type where
 field
  _==_ : A → A → Bool
