Comical markings for cubical sets.

A marking on a cubical set assigns to each face operator a trie value
(`ll`, `mm`, or `rr`) indicating whether that face is *left-marked*,
*free*, or *right-marked*. The **comical marking** condition, from
Doherty--Kapulkin--Maehara, asks that no face be *excluded* in the
sense of Definition 5.19.

This module defines the type-theoretic predicates (`Has-excluded`,
`is-comical-marked`, etc.) as well as Boolean decision procedures
for computation.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.CSet.Marking where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool
open Bool using (_&&_; _||_)
open import Core.Data.Empty
open import Core.Data.Nat
open import Core.Data.List

open import Data.Trie

open Nat using (_<_; _≤_; s<s; suc; step; _-_)

private variable
  m n k : Nat

```

## Lookup and endpoint conversion

The `look` function indexes into a marking list, returning `mm` (free)
for out-of-bounds positions. The `e->t` function converts a Boolean
endpoint to the corresponding trie value.

```agda

look : List Trie -> Nat -> Trie
look []       _     = mm
look (x ∷ _)  Z     = x
look (_ ∷ xs) (S k) = look xs k

ε→t : Bool -> Trie
ε→t false = ll
ε→t true  = rr

```

## Chain ordering

A chain witnesses that a face is excluded by finding a *target*
position carrying the matching endpoint, with all intermediate
positions carrying the *opposite* endpoint. The `Ordered` predicate
captures the direction (upward or downward), and `In-range` captures
the interior constraint.

```agda

Ordered : Bool -> Nat -> Nat -> Type 0ℓ
Ordered true  p t = S p ≤ t
Ordered false p t = S t ≤ p

In-range : Bool -> Nat -> Nat -> Nat -> Type 0ℓ
In-range true  p t k = (S p ≤ k) × (S k ≤ t)
In-range false p t k = (S t ≤ k) × (S k ≤ p)

```

## Chain record

A chain from position `p` in direction `d` witnesses an excluded face
by exhibiting a target and verifying the marking at all intermediate
positions.

```agda

record Chain
    (χ : List Trie) (ε : Bool) (p : Nat) (d : Bool)
    : Type 0ℓ where
  no-eta-equality
  field
    target   : Nat
    ordered  : Ordered d p target
    at-target : look χ target ≡ ε→t ε
    interior : ∀ k -> In-range d p target k
             -> look χ k ≡ Trie.flip (ε→t ε)

```

## Excluded witness dispatch

The witness type dispatches on the marking at position `p`. If the
marking is `mm` (free), the face is excluded when it carries *any*
endpoint value. If the marking is `ll` or `rr`, it is excluded
when there exists a chain in the appropriate direction.

```agda

Ex-witness : Trie -> List Trie -> Nat -> Bool -> Type 0ℓ
Ex-witness mm χ p ε = Σ b ∶ Bool , look χ p ≡ ε→t b
Ex-witness ll χ p ε = Chain χ ε p false
Ex-witness rr χ p ε = Chain χ ε p true

```

## Comical excluded and marking

A face at position `p` with endpoint `ε` is *excluded* when
there exists some trie value `k` witnessing exclusion. The
marking is *comical* when no face is excluded.

```agda

Has-excluded : List Trie -> Nat -> Bool -> Type 0ℓ
Has-excluded χ p ε = Σ k ∶ Trie , Ex-witness k χ p ε

is-comical-marked : List Trie -> Nat -> Bool -> Type 0ℓ
is-comical-marked χ p ε = ¬ Has-excluded χ p ε

```

## Strongly comical marking (Definition 5.21)

The strongly comical condition is a simplified variant for the
endpoint `ε = 1`. A strong witness is either that the face itself
carries an endpoint value, or (for the downward direction) that
the predecessor carries `rr`.

```agda

Strong-witness : Bool -> List Trie -> Nat -> Type 0ℓ
Strong-witness true  χ p     = Σ b ∶ Bool , look χ p ≡ ε→t b
Strong-witness false χ (S q) = look χ q ≡ rr
Strong-witness false χ Z     = ⊥

Has-strong-excl : List Trie -> Nat -> Type 0ℓ
Has-strong-excl χ p = Σ k ∶ Bool , Strong-witness k χ p

is-strongly-marked : List Trie -> Nat -> Type 0ℓ
is-strongly-marked χ p = ¬ Has-strong-excl χ p

```

## Boolean decision procedures

Trie equality as a Boolean.

```agda

eq-t : Trie -> Trie -> Bool
eq-t ll ll = true
eq-t ll mm = false
eq-t ll rr = false
eq-t mm ll = false
eq-t mm mm = true
eq-t mm rr = false
eq-t rr ll = false
eq-t rr mm = false
eq-t rr rr = true

```

Upward and downward scans. The upward scan uses a fuel argument
for structural termination. The downward scan recurses on the
position counter.

```agda

scan-up : List Trie -> Nat -> Trie -> Nat -> Bool
scan-up χ pos tgt Z        = false
scan-up χ pos tgt (S fuel) =
  let v = look χ pos in
  eq-t v tgt
    || (eq-t v (Trie.flip tgt)
        && scan-up χ (S pos) tgt fuel)

scan-down : List Trie -> Nat -> Trie -> Bool
scan-down χ Z        tgt = false
scan-down χ (S pos') tgt =
  let v = look χ pos' in
  eq-t v tgt
    || (eq-t v (Trie.flip tgt)
        && scan-down χ pos' tgt)

```

Full Boolean decision for exclusion and comicality.

```agda

has-excluded?
  : Nat -> List Trie -> Nat -> Bool -> Bool
has-excluded? n χ p ε =
  (Bool.not (eq-t (look χ p) mm)
    || scan-up χ (S p) (ε→t ε) (n - S p))
    || scan-down χ p (ε→t ε)

is-comical?
  : Nat -> List Trie -> Nat -> Bool -> Bool
is-comical? n χ p ε =
  Bool.not (has-excluded? n χ p ε)

```

Strongly comical Boolean decision.

```agda

has-strong? : List Trie -> Nat -> Bool
has-strong? χ p =
  Bool.not (eq-t (look χ p) mm)
    || check-below χ p
  where
    check-below : List Trie -> Nat -> Bool
    check-below χ Z     = false
    check-below χ (S q) = eq-t (look χ q) rr

is-strongly? : List Trie -> Nat -> Bool
is-strongly? χ p =
  Bool.not (has-strong? χ p)

```
