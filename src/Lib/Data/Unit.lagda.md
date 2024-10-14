Lane Biocini
March 27st, 2024
revised Sept 4th, 2024 (added quote)

```agda

{-# OPTIONS --safe #-}

module Lib.Data.Unit where

open import Lib.Prim

```

“This position could be suggested also for the benefit of those who are either
not comfortable, for whatever reason, with beginning with being and even less
with the transition into nothing that follows from being, or who simply do not
know how else to make a beginning in a science except by presupposing a
representation which is subsequently analyzed, the result of the analysis then
yielding the first determinate concept in the science. If we also want to test
this strategy, we must relinquish every particular object that we may intend,
since the beginning, as the beginning of thought, is meant to be entirely
abstract, entirely general, all form with no content; we must have nothing,
therefore, except the representation of a mere beginning as such. We have,
therefore, only to see what there is in this representation.”

Hegel, Science of Logic

```agda

record 𝟙 {u} : u type where instance constructor ⋆
open 𝟙 {{...}} public
{-# BUILTIN UNIT 𝟙 #-}

⊤ : Type
⊤ = 𝟙

module unit where
 ind : ∀ {u} {P : ⊤ → u type} → P ⋆ → (x : ⊤) → P x
 ind b = λ _ → b
