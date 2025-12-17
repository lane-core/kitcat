```
{-# OPTIONS --safe --cubical-compatible --two-level #-}

module Lib.Uninhabited where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Equal

record Uninhabited {u} (E : Type u) : Type u where
  constructor MkUninhabited
  field
    uninhabited : E → ⊥

  absurd : ∀ {v} {@0 A : Type v} → @0 E → A
  absurd e = ex-falso (uninhabited e)

open Uninhabited ⦃ ... ⦄ public
{-# INLINE MkUninhabited #-}
{-# DISPLAY Uninhabited.uninhabited _ = uninhabited #-}
{-# DISPLAY Uninhabited.absurd _ = absurd #-}

instance
  Uninhabited-nothing＝just : ∀ {u} {A : Type u} ⦃ E : Equal ⦄ {x : A}
                            → Uninhabited (nothing ＝ just x)
  Uninhabited-nothing＝just {A} {x = x} .Uninhabited.uninhabited p = {!!} where
    f : Maybe A → Type
    f (just x) = ⊤
    f nothing = ⊥
