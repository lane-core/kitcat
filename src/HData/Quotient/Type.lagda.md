Set quotients as a higher inductive type.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Quotient.Type where

open import Core.Type
open import Core.Base
open import Core.Data.Nat using (Nat; S)
open import Core.Trait.Trunc using (Trunc; set-trunc)

private variable
  u v : Level
```


## The quotient HIT

The set quotient `A / R` freely adds paths between related elements
while forcing the result to be a set.

```agda

data _/_ {u v} (A : Type u) (R : A → A → Type v) : Type (u ⊔ v) where
  [_]     : A → A / R
  quot    : {a b : A} → R a b → [ a ] ≡ [ b ]
  squash/ : is-set (A / R)

infix 5 _/_

instance
  Trunc-quotient : {A : Type u} {R : A → A → Type v} {k : Nat}
                 → Trunc (A / R) (S (S k))
  Trunc-quotient = set-trunc squash/
```


## Equivalence relations

```agda

record is-eqrel {u v} {A : Type u} (R : A → A → Type v) : Type (u ⊔ v) where
  field
    refl-eqrel  : {a : A} → R a a
    sym-eqrel   : {a b : A} → R a b → R b a
    trans-eqrel : {a b c : A} → R a b → R b c → R a c

open is-eqrel public
```
