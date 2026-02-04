Binary strings: induction, length, concatenation, flip, reverse.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Bin.Base where

open import Core.Type

open import Data.Bin.Type

open import Core.Data.Nat.Type

ind : ∀ {u} (P : Bin → Type u)
    → P []
    → (∀ {b} → P b → P (ll b))
    → (∀ {b} → P b → P (rr b))
    → ∀ b → P b
ind P e l r []     = e
ind P e l r (ll b) = l (ind P e l r b)
ind P e l r (rr b) = r (ind P e l r b)

length : Bin → Nat
length []     = Z
length (ll b) = S (length b)
length (rr b) = S (length b)

_++_ : Bin → Bin → Bin
[]     ++ ys = ys
ll x   ++ ys = ll (x ++ ys)
rr x   ++ ys = rr (x ++ ys)

infixr 5 _++_

flip : Bin → Bin
flip []     = []
flip (ll b) = rr (flip b)
flip (rr b) = ll (flip b)

reverse : Bin → Bin
reverse []     = []
reverse (ll b) = reverse b ++ ll []
reverse (rr b) = reverse b ++ rr []

```
