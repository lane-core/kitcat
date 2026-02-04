Basic operations on snoc lists.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.SnocList.Base where

open import Core.Type
open import Core.Data.Nat.Type

open import Data.SnocList.Type

ind : ∀ {u v} {A : Type u} (P : SnocList A -> Type v)
    -> P []
    -> ((xs : SnocList A) -> P xs -> (x : A) -> P (xs ∶< x))
    -> (xs : SnocList A) -> P xs
ind P nil snoc []        = nil
ind P nil snoc (xs ∶< x) = snoc xs (ind P nil snoc xs) x
{-# INLINE ind #-}

length : ∀ {u} {A : Type u} -> SnocList A -> Nat
length []        = Z
length (xs ∶< _) = S (length xs)
{-# INLINE length #-}

map : ∀ {u v} {A : Type u} {B : Type v}
    -> (A -> B) -> SnocList A -> SnocList B
map f []        = []
map f (xs ∶< x) = map f xs ∶< f x
{-# INLINE map #-}

infixl 5 _<><_
_<><_ : ∀ {u} {A : Type u}
      -> SnocList A -> SnocList A -> SnocList A
xs <>< []        = xs
xs <>< (ys ∶< y) = (xs <>< ys) ∶< y

foldr : ∀ {u v} {A : Type u} {B : Type v}
      -> (A -> B -> B) -> B -> SnocList A -> B
foldr f z []        = z
foldr f z (xs ∶< x) = foldr f (f x z) xs

foldl : ∀ {u v} {A : Type u} {B : Type v}
      -> (B -> A -> B) -> B -> SnocList A -> B
foldl f z []        = z
foldl f z (xs ∶< x) = f (foldl f z xs) x

reverse : ∀ {u} {A : Type u} -> SnocList A -> SnocList A
reverse = ind _ [] (λ _ acc x -> cons-front x acc) where
  cons-front : ∀ {u} {A : Type u}
             -> A -> SnocList A -> SnocList A
  cons-front x []        = [] ∶< x
  cons-front x (ys ∶< y) = cons-front x ys ∶< y

```
