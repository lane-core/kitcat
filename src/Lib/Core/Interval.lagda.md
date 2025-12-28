```agda

{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}

module Lib.Core.Interval where

open import Lib.Core.Prim using (Type; Level)
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Core.HCompU
open import Lib.Core.Equiv

htransport : ∀ {u} (P : Htpy (λ _ → Type u)) → P i0 → P i1
htransport = coe01
{-# INLINE htransport #-}

hrefl : {x : A} → Htpy (λ _ → A)
hrefl {x = x} _ = x

Cube : ∀ {u} → Nat → Type (u ₊)
Cube {u} Z = Type u
Cube (S n) = I → Cube n

Line : u → Type₊ u
Line u = Cube n

-- app : ∀ {u v} {A : I → Type u} {B : ∀ i → A i → Type v}
--     → (f : ∀ {i} (x : A i) → B i x) (p : Htpy A) → Htpy (λ i → B i (p i))
-- app f p i = f (p i)
