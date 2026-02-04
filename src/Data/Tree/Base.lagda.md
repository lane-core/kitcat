Binary trees: eliminator, recursor, map, size, depth, fold, flatten.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Tree.Base where

open import Core.Type

open import Data.Tree.Type

open import Core.Data.Nat.Type
open import Core.Data.Nat.Base using (_+_)
open import Core.Data.List.Type
open import Core.Data.List.Base using (_++_)

private variable
  u v : Level
  A B C : Type u
```

## Eliminator

```agda

ind : (P : Tree A → Type v)
    → (∀ a → P (leaf a))
    → (∀ {l r} → P l → P r → P (node l r))
    → ∀ t → P t
ind P lf nd (leaf a)   = lf a
ind P lf nd (node l r) = nd (ind P lf nd l) (ind P lf nd r)
```

## Recursor

```agda

rec : (A → B) → (B → B → B) → Tree A → B
rec f g (leaf a)   = f a
rec f g (node l r) = g (rec f g l) (rec f g r)
```

## Map

```agda

tree-map : (A → B) → Tree A → Tree B
tree-map f (leaf a)   = leaf (f a)
tree-map f (node l r) = node (tree-map f l) (tree-map f r)
```

## Size and depth

```agda

private
  max : Nat → Nat → Nat
  max Z     n     = n
  max (S m) Z     = S m
  max (S m) (S n) = S (max m n)

size : Tree A → Nat
size (leaf _)   = 0
size (node l r) = S (size l + size r)

leaves : Tree A → Nat
leaves (leaf _)   = 1
leaves (node l r) = leaves l + leaves r

depth : Tree A → Nat
depth (leaf _)   = 0
depth (node l r) = S (max (depth l) (depth r))

ldepth : Tree A → Nat
ldepth (leaf _)   = 0
ldepth (node l r) = max (S (ldepth l)) (ldepth r)
```

## Fold and flatten

```agda

fold : (A → B → B) → B → Tree A → B
fold f z (leaf a)   = f a z
fold f z (node l r) = fold f (fold f z r) l

flatten : Tree A → List A
flatten (leaf a)   = a ∷ []
flatten (node l r) = flatten l ++ flatten r
```

## Mirror

```agda

mirror : Tree A → Tree A
mirror (leaf a)   = leaf a
mirror (node l r) = node (mirror r) (mirror l)
```
