List operations: length, map, append, fold, and derived combinators.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.List.Base where

open import Core.Type
open import Core.Data.List.Type

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)

private variable
  u v w : Level
  A B C : Type u

length : List A → Nat
length []       = zero
length (_ ∷ xs) = suc (length xs)

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

foldr : (A → B → B) → B → List A → B
foldr f z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldl : (B → A → B) → B → List A → B
foldl f z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f xs = concat (map f xs)

reverse : List A → List A
reverse = foldl (λ acc x → x ∷ acc) []

filter : (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs

replicate : Nat → A → List A
replicate zero    _ = []
replicate (suc n) x = x ∷ replicate n x

```
