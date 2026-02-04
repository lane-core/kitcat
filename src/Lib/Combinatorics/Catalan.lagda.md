Catalan numbers and depth-bounded Catalan numbers.

The standard Catalan recurrence: C(0) = 1, C(n+1) = sum over i
from 0 to n of C(i) * C(n-i). The depth-bounded variant T(n,k)
counts binary trees with n internal nodes and depth at most k.
The asymmetric variant Ta(n,k) counts trees with left-depth at
most k, where only left-child descents count toward depth.

All three are defined using course-of-values recursion over a
snoc-list table of previously computed values.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Combinatorics.Catalan where

open import Core.Data.Nat.Type using (Nat; Z; S)
open import Core.Data.Nat.Base using (_+_; _*_; _-_)
open import Core.Base using (_≡_; refl)
open import Core.Type using (Type; 0ℓ)
```

## Tables for course-of-values recursion

We represent previously computed values as a snoc-list. The most
recently appended value sits at index 0; older entries have
higher indices.

```agda

data Table : Type 0ℓ where
  []  : Table
  _▸_ : Table → Nat → Table

infixl 5 _▸_

lookup : Table → Nat → Nat
lookup []      _     = 0
lookup (t ▸ v) Z     = v
lookup (t ▸ v) (S k) = lookup t k
```

## Convolution

Given a table `t` containing values f(0) through f(n) (stored
in reverse: f(n) at index 0, f(0) at index n), compute the sum
from i = 0 to k of f(i) * f(n - i).

```agda

tconv : Table → Nat → Nat → Nat
tconv t n Z     = lookup t n * lookup t 0
tconv t n (S k) = lookup t (n - S k) * lookup t (S k)
                  + tconv t n k
```


## Catalan numbers

Build the table C(0), C(1), ..., C(n) using the recurrence
C(0) = 1 and C(n+1) = sum from i=0 to n of C(i) * C(n-i).

```agda

cat-table : Nat → Table
cat-table Z     = [] ▸ 1
cat-table (S n) =
  let t = cat-table n
  in t ▸ tconv t n n

C : Nat → Nat
C n = lookup (cat-table n) 0
```


## Depth-bounded Catalan numbers

T(n, k) counts binary trees with n internal nodes and depth at
most k. The recurrence is: T(0, k) = 1, T(n+1, 0) = 0,
T(n+1, k+1) = sum from i=0 to n of T(i, k) * T(n-i, k).

A tree of depth at most k+1 has a root node whose subtrees
each have depth at most k, hence the depth bound decreases in
the subtree calls.

We build tables of T(0,k), ..., T(n,k) by structural recursion
on n and k. For T(n+1, k+1), we need the full table at depth k
to compute the convolution.

```agda

t-table : Nat → Nat → Table
t-table Z     _     = [] ▸ 1
t-table (S n) Z     = t-table n Z ▸ 0
t-table (S n) (S k) =
  let prev = t-table n k
  in t-table n (S k) ▸ tconv prev n n

T : Nat → Nat → Nat
T n k = lookup (t-table n k) 0
```


## Left-depth-bounded Catalan numbers

Ta(n, k) counts binary trees with n internal nodes and
left-depth at most k, where left-depth counts only left-child
descents: ldepth(leaf) = 0, ldepth(node(l,r)) = max(1 +
ldepth(l), ldepth(r)). The recurrence is asymmetric: Ta(0, k)
= 1, Ta(n+1, 0) = 0, Ta(n+1, k+1) = sum from i=0 to n of
Ta(i, k) * Ta(n-i, k+1). The right factor stays at depth k+1
because going right does not increase nesting depth. This is
the coefficient of x^n in the continued fraction
R_k = 1/(1 - x * R_{k-1}).

The convolution takes two tables: `prev` for the left factor
(depth k) and `curr` for the right factor (depth k+1, being
built).

```agda

ta-conv : Table → Table → Nat → Nat → Nat
ta-conv prev curr n Z     = lookup prev n * lookup curr 0
ta-conv prev curr n (S k) =
  lookup prev (n - S k) * lookup curr (S k)
  + ta-conv prev curr n k

ta-table : Nat → Nat → Table
ta-table Z     _     = [] ▸ 1
ta-table (S n) Z     = ta-table n Z ▸ 0
ta-table (S n) (S k) =
  let prev = ta-table n k
      curr = ta-table n (S k)
  in curr ▸ ta-conv prev curr n n

Ta : Nat → Nat → Nat
Ta n k = lookup (ta-table n k) 0
```


## Computational checks

```agda

_ : C 0 ≡ 1
_ = refl

_ : C 1 ≡ 1
_ = refl

_ : C 2 ≡ 2
_ = refl

_ : C 3 ≡ 5
_ = refl

_ : C 4 ≡ 14
_ = refl

_ : C 5 ≡ 42
_ = refl

_ : T 0 0 ≡ 1
_ = refl

_ : T 1 0 ≡ 0
_ = refl

_ : T 1 1 ≡ 1
_ = refl

_ : T 2 2 ≡ 2
_ = refl

_ : T 3 2 ≡ 1
_ = refl

_ : T 3 3 ≡ 5
_ = refl

_ : T 4 3 ≡ 6
_ = refl

_ : T 5 4 ≡ 26
_ = refl

_ : C 5 - T 5 4 ≡ 16
_ = refl

_ : Ta 0 0 ≡ 1
_ = refl

_ : Ta 1 0 ≡ 0
_ = refl

_ : Ta 1 1 ≡ 1
_ = refl

_ : Ta 2 1 ≡ 1
_ = refl

_ : Ta 2 2 ≡ 2
_ = refl

_ : Ta 3 2 ≡ 4
_ = refl

_ : Ta 3 3 ≡ 5
_ = refl

_ : Ta 4 3 ≡ 13
_ = refl

_ : Ta 4 4 ≡ 14
_ = refl

_ : Ta 5 4 ≡ 41
_ = refl

_ : C 5 - Ta 5 4 ≡ 1
_ = refl

_ : Ta 6 4 ≡ 122
_ = refl
```
