```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Data.Unit where

open import Prim.Type

```

Level polymorphic unit, using Lift

```

𝟙 : ∀ {ℓ} → Type ℓ
𝟙 {ℓ} = Lift ℓ ⊤
{-# DISPLAY Lift ℓ ⊤ = 𝟙 {ℓ} #-}

pattern ✶ = lift tt

module _ {ℓ ℓ'} (P : 𝟙 {ℓ} → Type ℓ') (p : P ✶) where
  𝟙-ind : (x : 𝟙) → P x
  𝟙-ind ._ = p

instance
  tt' : ∀ {ℓ} → 𝟙 {ℓ}
  tt' = ✶
