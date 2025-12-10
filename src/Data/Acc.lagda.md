```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Acc where

open import Lib.Type
open import Lib.Cubical.Base
open import Lib.Path
open import Lib.Nat hiding (ind)

data Acc {u v} {A : Type u} (_<_ : A → A → Type v) : A → Type (u ⊔ v) where
  step : (a : A) → ((x : A) → x < a → Acc _<_ x) → Acc _<_ a

private variable
  u v : Level
  A : Type u

module acc (_<_ : A → A → Type v) where
  ind : (P : A → Type u)
      → ((a0 : A) → Acc _<_ a0 → ((a : A) → a < a0 → P a) → P a0)
      → (a0 : A) → Acc _<_ a0 → P a0
  ind P s a0 (step a f) = s a (step a0 f) λ a1 q → ind P s a1 (f a1 q)

  is-wellfounded = (a : A) → Acc _<_ a


by-equality : (x y : A)
            → ((a0 : A) → Acc _≡_ a0 → ((a : A) → a ≡ a0 → a ≡ y) → a0 ≡ y)
            → Acc _≡_ x → x ≡ y
by-equality x y s p = acc.ind _≡_ (_≡ y) s x p
