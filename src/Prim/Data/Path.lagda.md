```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Data.Path where

open import Prim.Type

--infixr 2 pathp-syntax

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_ to infix 2 _＝_ )

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ _ → A)

path-syntax : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
path-syntax A = PathP (λ _ → A)
syntax path-syntax A x y = x ＝ y ∶ A

-- pathp-syntax : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
-- pathp-syntax = PathP
-- syntax pathp-syntax (λ i → b) x y = ∂ i ↦ b , x ＝ y

-- --{-# INLINE pathp-syntax #-}
-- --{-# DISPLAY pathp-syntax A x y = PathP A x y #-}

-- ap : ∀ {u v} {A : Type u} {B : A → Type v}
--    → (f : ∀ a → B a)
--    → {x y : A}
--    → (p : x ＝ y)
--    → ∂ i ↦ B (p i) , f x ＝ f y
-- ap f p i = f (p i)
-- {-# INLINE ap #-}
```
