Properties and lemmas for lists.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Properties where

open import Core.Type hiding (id)
open import Core.Base using (_≡_; refl; ap; sym)
open import Core.Kan using (_∙_)
open import Core.Data.List.Type
open import Core.Data.List.Base

private variable
  u v w : Level
  A B C : Type u

```

## map

```agda

module map where
  id : (xs : List A) → map (λ x → x) xs ≡ xs
  id [] = refl
  id (x ∷ xs) i = x ∷ id xs i

  comp
    : (f : B → C) (g : A → B) (xs : List A)
    → map (f ∘ g) xs ≡ (map f ∘ map g) xs
  comp f g [] = refl
  comp f g (x ∷ xs) i = f (g x) ∷ comp f g xs i

  cat
    : (f : A → B) (xs ys : List A)
    → map f (xs ++ ys) ≡ (map f xs ++ map f ys)
  cat f [] ys = refl
  cat f (x ∷ xs) ys i = f x ∷ cat f xs ys i

```

## cat (append)

```agda

module cat where
  unitr : (xs : List A) → (xs ++ []) ≡ xs
  unitr [] = refl
  unitr (x ∷ xs) i = x ∷ unitr xs i

  assoc
    : (xs ys zs : List A)
    → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  assoc [] ys zs = refl
  assoc (x ∷ xs) ys zs i = x ∷ assoc xs ys zs i

```

## concat

```agda

module concat where
  cat
    : (xss yss : List (List A))
    → concat (xss ++ yss) ≡ (concat xss ++ concat yss)
  cat [] yss = refl
  cat (xs ∷ xss) yss =
    ap (xs ++_) (cat xss yss)
    ∙ sym (cat.assoc xs (concat xss) (concat yss))

```

## concatMap

```agda

module concatMap where
  cat
    : (f : A → List B) (xs ys : List A)
    → concatMap f (xs ++ ys)
      ≡ (concatMap f xs ++ concatMap f ys)
  cat f xs ys =
    ap concat (map.cat f xs ys)
    ∙ concat.cat (map f xs) (map f ys)

  singleton
    : (f : A → List B) (x : A)
    → concatMap f (x ∷ []) ≡ f x
  singleton f x = cat.unitr (f x)

  unitr : (xs : List A) → concatMap (_∷ []) xs ≡ xs
  unitr [] = refl
  unitr (x ∷ xs) i = x ∷ unitr xs i

  assoc
    : (f : A → List B) (g : B → List C) (xs : List A)
    → concatMap g (concatMap f xs)
      ≡ concatMap (λ x → concatMap g (f x)) xs
  assoc f g [] = refl
  assoc f g (x ∷ xs) =
    cat g (f x) (concatMap f xs)
    ∙ ap (concatMap g (f x) ++_) (assoc f g xs)

```
