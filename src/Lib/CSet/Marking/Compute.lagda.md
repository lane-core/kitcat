Enumeration and verification of comical marking counts.

This module generates all 3^n marking characteristics, filters by
dimension (count of free entries), and verifies counts against
Doherty--Kapulkin--Maehara's Table 1 (comical) and Table 2
(strongly comical) via definitional equality.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.CSet.Marking.Compute where

open import Core.Type
open import Core.Base
open import Core.Data.Nat
open import Core.Data.List
open import Core.Data.Bool

open List

open import Data.Trie

open import Lib.CSet.Marking

open Nat using (_+_; _-_; EqBool)

```

## Enumeration

Generate all 3^n marking characteristics as lists of trie values.
The order places `mm` (free) first so free dimensions are preferred.

```agda

all-chars : Nat -> List (List Trie)
all-chars Z     = [] ∷ []
all-chars (S n) = concatMap
  (λ prev →
    (mm ∷ prev) ∷ (ll ∷ prev) ∷ (rr ∷ prev) ∷ [])
  (all-chars n)

```

## Dimension filter

Count free (`mm`) entries in a characteristic, then filter to those
with exactly `m` free entries.

```agda

count-free : List Trie -> Nat
count-free []         = Z
count-free (mm ∷ xs)  = S (count-free xs)
count-free (ll ∷ xs)  = count-free xs
count-free (rr ∷ xs)  = count-free xs

chars-of-dim : Nat -> Nat -> List (List Trie)
chars-of-dim n m =
  filter (λ χ → EqBool (count-free χ) m)
    (all-chars n)

```

## Counting

Count comical-marked and strongly-marked characteristics at a given
dimension.

```agda

count-comical : Nat -> Nat -> Bool -> Nat -> Nat
count-comical n p ε m =
  length
    (filter (λ χ → is-comical? n χ p ε)
      (chars-of-dim n m))

count-strongly : Nat -> Nat -> Nat -> Nat
count-strongly n p m =
  length
    (filter (λ χ → is-strongly? χ p)
      (chars-of-dim n m))

```

## Verification: comical table (paper Table 1)

Counts for the comical marking condition on the n-cube,
verified by definitional computation.

```agda

-- n = 2
_ : count-comical 2 0 true 2 ≡ 1
_ = refl

_ : count-comical 2 0 true 1 ≡ 1
_ = refl

_ : count-comical 2 1 true 1 ≡ 1
_ = refl

-- n = 3
_ : count-comical 3 0 true 3 ≡ 1
_ = refl

_ : count-comical 3 0 true 2 ≡ 3
_ = refl

_ : count-comical 3 0 true 1 ≡ 1
_ = refl

_ : count-comical 3 1 true 2 ≡ 2
_ = refl

_ : count-comical 3 1 true 1 ≡ 1
_ = refl

_ : count-comical 3 2 true 2 ≡ 3
_ = refl

_ : count-comical 3 2 true 1 ≡ 1
_ = refl

```

## Verification: strongly comical table (paper Table 2)

Counts for the strongly comical marking condition.

```agda

-- n = 2
_ : count-strongly 2 0 2 ≡ 1
_ = refl

_ : count-strongly 2 0 1 ≡ 2
_ = refl

_ : count-strongly 2 1 1 ≡ 1
_ = refl

-- n = 3
_ : count-strongly 3 0 3 ≡ 1
_ = refl

_ : count-strongly 3 0 2 ≡ 4
_ = refl

_ : count-strongly 3 0 1 ≡ 4
_ = refl

_ : count-strongly 3 1 2 ≡ 3
_ = refl

_ : count-strongly 3 1 1 ≡ 2
_ = refl

_ : count-strongly 3 2 2 ≡ 3
_ = refl

_ : count-strongly 3 2 1 ≡ 2
_ = refl

```
