Marking counts and a 2-state automaton for depth-bounded
Catalan numbers at depth 4.

The symmetric marking count M(n,i) = T(i,4) * T(n-i,4) gives
the contribution from splitting a tree with n+1 internal nodes
at the root such that the left subtree has i internal nodes
and the right has n-i, both constrained to depth at most 4.
The sum over i=0..n recovers T(n+1, 5).

The asymmetric marking count Ma(n,i) = Ta(i,3) * Ta(n-i,4)
gives the analogous contribution for left-depth-bounded trees:
the left subtree has left-depth at most 3 (one level down from
root) and the right subtree has left-depth at most 4 (going
right is free). The sum over i=0..n recovers Ta(n+1, 4).

The 2-state chain automaton tracks whether a depth violation
has occurred along a sequence of subtree inspections.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Combinatorics.Catalan.Factorization where

open import Core.Data.Nat.Type using (Nat; Z; S)
open import Core.Data.Nat.Base using (_+_; _*_; _-_; EqBool)
open import Core.Base using (_≡_; refl)
open import Core.Type using (Type; 0ℓ)

open import Lib.Combinatorics.Catalan using (C; T; Ta)
open import Core.Data.Bool using (Bool; true; false)

private
  not : Bool → Bool
  not false = true
  not true  = false
```


## Marking count

M(n, i) counts the contribution from one split of a tree
with n+1 internal nodes at the root: i nodes go left and
n - i go right, both constrained to depth at most 4.

```agda

M : Nat → Nat → Nat
M n i = T i 4 * T (n - i) 4
```


## Asymmetric marking count

Ma(n, i) counts the contribution from one split of a tree
with n+1 internal nodes at the root: i nodes go left and
n - i go right. The left subtree has left-depth at most 3
(one level down from root) and the right subtree has
left-depth at most 4 (going right does not increase
left-depth).

```agda

Ma : Nat → Nat → Nat
Ma n i = Ta i 3 * Ta (n - i) 4
```


## Computational checks for Ma

Verify that the sum of Ma(n,i) for i = 0..n equals
Ta(n+1, 4), the number of trees with n+1 internal nodes
and left-depth at most 4.

```agda

sum-Ma : Nat → Nat → Nat
sum-Ma n Z     = Ma n 0
sum-Ma n (S k) = Ma n (S k) + sum-Ma n k

_ : sum-Ma 0 0 ≡ Ta 1 4
_ = refl

_ : sum-Ma 1 1 ≡ Ta 2 4
_ = refl

_ : sum-Ma 2 2 ≡ Ta 3 4
_ = refl

_ : sum-Ma 3 3 ≡ Ta 4 4
_ = refl

_ : sum-Ma 4 4 ≡ Ta 5 4
_ = refl
```


## Left-depth violation predicate

A predicate that flags whether position i contributes a
left-depth violation: we flag `true` when Ta(i,3) differs
from Ta(i,4), meaning some trees at that size have
left-depth exactly 4.

```agda

exceeds-ldepth-3 : Nat → Bool
exceeds-ldepth-3 n = not (EqBool (Ta n 3) (Ta n 4))
```


## Chain automaton

A simple 2-state automaton that processes a sequence of Boolean
flags indicating whether each subtree exceeds the depth bound.
The automaton starts in the `unbroken` state and transitions to
`broken` upon encountering a violation; once broken, it stays
broken.

```agda

data ChainState : Type 0ℓ where
  broken unbroken : ChainState

step : ChainState → Bool → ChainState
step broken  false = broken
step broken  true  = broken
step unbroken false = unbroken
step unbroken true  = broken
```

Run the automaton over a sequence of Booleans generated from a
predicate on indices 0 through n.

```agda

run : ChainState → (Nat → Bool) → Nat → ChainState
run s f Z     = step s (f Z)
run s f (S n) = run (step s (f Z)) (λ k → f (S k)) n

is-unbroken : ChainState → Nat
is-unbroken unbroken = 1
is-unbroken broken   = 0
```

A predicate that flags whether position i contributes a
depth violation: we flag `true` when T(i,3) differs from
T(i,4), meaning some trees at that size have depth exactly 4.

```agda

exceeds-depth-3 : Nat → Bool
exceeds-depth-3 n = not (EqBool (T n 3) (T n 4))
```


## Computational checks for M

Verify that sum of M(n,i) for i = 0..n equals T(n+1, 5), the
number of trees with n+1 internal nodes and depth at most 5.

```agda

sum-M : Nat → Nat → Nat
sum-M n Z     = M n 0
sum-M n (S k) = M n (S k) + sum-M n k

_ : M 0 0 ≡ T 0 4 * T 0 4
_ = refl

_ : M 1 0 ≡ T 0 4 * T 1 4
_ = refl

_ : M 1 1 ≡ T 1 4 * T 0 4
_ = refl

_ : sum-M 0 0 ≡ T 1 5
_ = refl

_ : sum-M 1 1 ≡ T 2 5
_ = refl

_ : sum-M 2 2 ≡ T 3 5
_ = refl

_ : sum-M 3 3 ≡ T 4 5
_ = refl

_ : sum-M 4 4 ≡ T 5 5
_ = refl
```

## Chain automaton checks

```agda

_ : step unbroken false ≡ unbroken
_ = refl

_ : step unbroken true ≡ broken
_ = refl

_ : step broken false ≡ broken
_ = refl

_ : step broken true ≡ broken
_ = refl
```
