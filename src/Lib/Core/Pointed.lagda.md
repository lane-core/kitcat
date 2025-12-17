```agda

{-# OPTIONS --safe --erased-cubical #-}

module Lib.Pointed where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base

Type* : ∀ u → Type (u ₊)
Type* u = Σ A :: Type u , A

pt : ∀ {u} (A : Type* u) → A .fst
pt = snd

instance
  Underlying-Type* : ∀ {u} → Underlying (Type* u)
  Underlying-Type* {u} .Underlying.ℓ-underlying = u
  Underlying-Type* .Underlying.⌞_⌟ A = A .fst

Loop : ∀ {u} → Type* u → Type* u
Loop (_ , a) .fst = a ≡ a
Loop (_ , a) .snd _ = a

Ω : ∀ {u} → Type* u → Type u
Ω (_ , a) = a ≡ a
