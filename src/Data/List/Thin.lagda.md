```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Data.List.Thin where

open import Lib.Type
open import Data.List

pattern _:<_ x xs = xs ∷ x
infixl 8 _:<_

data Thin {u} {A : Type u} : List A → List A → Type u where
  done : Thin [] []
  keep : ∀ {xs ys} → Thin xs ys → ∀ k → Thin (xs :< k) (ys :< k)
  drop : ∀ {xs ys} → Thin xs ys → ∀ {k} → Thin xs (ys :< k)
