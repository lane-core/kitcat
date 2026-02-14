Properties of snoc list operations.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Data.SnocList.Properties where

open import Core.Base
open import Core.Type hiding (id)

open import Data.SnocList.Type
open import Data.SnocList.Base

```

## map

```agda

module map where
  id : ∀ {u} {A : Type u} (xs : SnocList A)
     -> map (λ x -> x) xs ≡ xs
  id []        = refl
  id (xs ∶< x) = ap (_∶< x) (id xs)

```

## _<><_

```agda

module _<><_ where
  unitr : ∀ {u} {A : Type u} (xs : SnocList A)
       -> xs <>< [] ≡ xs
  unitr xs = refl

  unitl : ∀ {u} {A : Type u} (xs : SnocList A)
       -> [] <>< xs ≡ xs
  unitl []        = refl
  unitl (xs ∶< x) = ap (_∶< x) (unitl xs)

  assoc : ∀ {u} {A : Type u} (xs ys zs : SnocList A)
        -> xs <>< (ys <>< zs) ≡ (xs <>< ys) <>< zs
  assoc xs ys []        = refl
  assoc xs ys (zs ∶< z) = ap (_∶< z) (assoc xs ys zs)

```
