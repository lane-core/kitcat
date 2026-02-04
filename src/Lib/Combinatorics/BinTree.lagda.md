Binary trees with size (internal node count), depth (longest
root-to-leaf path), and left-depth (associativity nesting depth).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Combinatorics.BinTree where

open import Core.Data.Nat.Type using (Nat; Z; S)
open import Core.Data.Nat.Base using (_+_)
open import Core.Base using (_≡_; refl)
open import Core.Type using (Type; 0ℓ)
```

## Maximum

```agda

max : Nat → Nat → Nat
max Z     n     = n
max (S m) Z     = S m
max (S m) (S n) = S (max m n)
```

## Binary trees

```agda

data BinTree : Type 0ℓ where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

size : BinTree → Nat
size leaf       = 0
size (node l r) = S (size l + size r)

depth : BinTree → Nat
depth leaf       = 0
depth (node l r) = S (max (depth l) (depth r))
```

## Left-depth

The left-depth counts associativity nesting depth: going left costs 1,
going right is free. In the bracketing correspondence, the left child
encodes "nest the associator deeper" while the right child encodes
"continue composing at the current level."

```agda

ldepth : BinTree → Nat
ldepth leaf       = 0
ldepth (node l r) = max (S (ldepth l)) (ldepth r)
```

## Computational checks

```agda

_ : size leaf ≡ 0
_ = refl

_ : size (node leaf leaf) ≡ 1
_ = refl

_ : depth leaf ≡ 0
_ = refl

_ : depth (node leaf leaf) ≡ 1
_ = refl

_ : depth (node (node leaf leaf) leaf) ≡ 2
_ = refl

_ : ldepth leaf ≡ 0
_ = refl

_ : ldepth (node leaf leaf) ≡ 1
_ = refl

_ : ldepth (node (node leaf leaf) leaf) ≡ 2
_ = refl

_ : ldepth (node leaf (node leaf leaf)) ≡ 1
_ = refl

_ : ldepth (node (node (node leaf leaf) leaf) leaf) ≡ 3
_ = refl
```
