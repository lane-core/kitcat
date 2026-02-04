Properties and proofs for binary strings.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Data.Bin.Properties where

open import Core.Base
open import Core.Type
open import Core.Kan hiding (assoc)
open import Core.Transport
open import Core.Data.Dec
open Dec
open import Core.Data.Empty

open import Data.Bin.Type
open import Data.Bin.Base

private variable
  a b c : Bin

```

## Decidable equality

Discriminators distinguish the three constructors pairwise. Head
extractors recover the recursive argument.

```agda

private
  ll-head : Bin → Bin
  ll-head []     = []
  ll-head (ll b) = b
  ll-head (rr _) = []

  rr-head : Bin → Bin
  rr-head []     = []
  rr-head (ll _) = []
  rr-head (rr b) = b

DecEq-Bin : (x y : Bin) → Dec (x ≡ y)
DecEq-Bin []     []     = yes refl
DecEq-Bin []     (ll _) = no (λ p → subst f p tt) where f = λ { [] → ⊤ ; (ll _) → ⊥ ; (rr _) → ⊤ }
DecEq-Bin []     (rr _) = no (λ p → subst f p tt) where f = λ { [] → ⊤ ; (ll _) → ⊤ ; (rr _) → ⊥ }
DecEq-Bin (ll _) []     = no (λ p → subst f p tt) where f = λ { [] → ⊥ ; (ll _) → ⊤ ; (rr _) → ⊤ }
DecEq-Bin (rr _) []     = no (λ p → subst f p tt) where f = λ { [] → ⊥ ; (ll _) → ⊤ ; (rr _) → ⊤ }
DecEq-Bin (ll _) (rr _) = no (λ p → subst f p tt) where f = λ { [] → ⊤ ; (ll _) → ⊤ ; (rr _) → ⊥ }
DecEq-Bin (rr _) (ll _) = no (λ p → subst f p tt) where f = λ { [] → ⊤ ; (ll _) → ⊥ ; (rr _) → ⊤ }
DecEq-Bin (ll x) (ll y) with DecEq-Bin x y
... | yes p = yes (ap ll p)
... | no ¬p = no λ q → ¬p (ap ll-head q)
DecEq-Bin (rr x) (rr y) with DecEq-Bin x y
... | yes p = yes (ap rr p)
... | no ¬p = no λ q → ¬p (ap rr-head q)

set : is-set Bin
set = hedberg DecEq-Bin

```

## Concatenation properties

```agda

module concat where
  unitl : ∀ b → [] ++ b ≡ b
  unitl _ = refl

  unitr : ∀ b → b ++ [] ≡ b
  unitr []     = refl
  unitr (ll b) = ap ll (unitr b)
  unitr (rr b) = ap rr (unitr b)

  assoc : ∀ a b c → a ++ (b ++ c) ≡ (a ++ b) ++ c
  assoc []     b c = refl
  assoc (ll a) b c = ap ll (assoc a b c)
  assoc (rr a) b c = ap rr (assoc a b c)

```

## Flip

```agda

module flip where
  invol : ∀ b → flip (flip b) ≡ b
  invol []     = refl
  invol (ll b) = ap ll (invol b)
  invol (rr b) = ap rr (invol b)

  over-++ : ∀ a b → flip (a ++ b) ≡ flip a ++ flip b
  over-++ []     b = refl
  over-++ (ll a) b = ap rr (over-++ a b)
  over-++ (rr a) b = ap ll (over-++ a b)

```
