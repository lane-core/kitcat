Properties and proofs for booleans.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Bool.Properties where

open import Core.Base
open import Core.Type
open import Core.Transport
open import Core.Data.Dec
open Dec
open import Core.Data.Empty
open import Core.Data.Bool.Type
open import Core.Data.Bool.Base

```

## Decidable equality and set

```agda

DecEq-Bool : (x y : Bool) → Dec (x ≡ y)
DecEq-Bool true  true  = yes refl
DecEq-Bool true  false = no (λ p → subst f p tt) where f = λ { true → ⊤ ; false → ⊥ }
DecEq-Bool false true  = no (λ p → subst f p tt) where f = λ { true → ⊥ ; false → ⊤ }
DecEq-Bool false false = yes refl

set : is-set Bool
set = hedberg DecEq-Bool

```

## Negation

```agda

module not where
  invol : ∀ b → not (not b) ≡ b
  invol true  = refl
  invol false = refl

```

## Conjunction

```agda

module and where
  comm : ∀ a b → and a b ≡ and b a
  comm true  true  = refl
  comm true  false = refl
  comm false true  = refl
  comm false false = refl

  assoc : ∀ a b c → and a (and b c) ≡ and (and a b) c
  assoc true  b c = refl
  assoc false b c = refl

  idem : ∀ a → and a a ≡ a
  idem true  = refl
  idem false = refl

  unitl : ∀ b → and true b ≡ b
  unitl b = refl

  unitr : ∀ b → and b true ≡ b
  unitr true  = refl
  unitr false = refl

  zerol : ∀ b → and false b ≡ false
  zerol b = refl

  zeror : ∀ b → and b false ≡ false
  zeror true  = refl
  zeror false = refl

```

## Disjunction

```agda

module or where
  comm : ∀ a b → or a b ≡ or b a
  comm true  true  = refl
  comm true  false = refl
  comm false true  = refl
  comm false false = refl

  assoc : ∀ a b c → or a (or b c) ≡ or (or a b) c
  assoc true  b c = refl
  assoc false b c = refl

  idem : ∀ a → or a a ≡ a
  idem true  = refl
  idem false = refl

  unitl : ∀ b → or false b ≡ b
  unitl b = refl

  unitr : ∀ b → or b false ≡ b
  unitr true  = refl
  unitr false = refl

  zerol : ∀ b → or true b ≡ true
  zerol b = refl

  zeror : ∀ b → or b true ≡ true
  zeror true  = refl
  zeror false = refl

```

## Exclusive-or

```agda

module xor where
  comm : ∀ a b → xor a b ≡ xor b a
  comm true  true  = refl
  comm true  false = refl
  comm false true  = refl
  comm false false = refl

  assoc : ∀ a b c → xor a (xor b c) ≡ xor (xor a b) c
  assoc true  true  true  = refl
  assoc true  true  false = refl
  assoc true  false true  = refl
  assoc true  false false = refl
  assoc false true  true  = refl
  assoc false true  false = refl
  assoc false false true  = refl
  assoc false false false = refl

  unitl : ∀ b → xor false b ≡ b
  unitl true  = refl
  unitl false = refl

  unitr : ∀ b → xor b false ≡ b
  unitr true  = refl
  unitr false = refl

  invol : ∀ a b → xor a (xor a b) ≡ b
  invol true  true  = refl
  invol true  false = refl
  invol false true  = refl
  invol false false = refl

```

## De Morgan

```agda

module de-morgan where
  not-and : ∀ a b → not (and a b) ≡ or (not a) (not b)
  not-and true  true  = refl
  not-and true  false = refl
  not-and false true  = refl
  not-and false false = refl

  not-or : ∀ a b → not (or a b) ≡ and (not a) (not b)
  not-or true  true  = refl
  not-or true  false = refl
  not-or false true  = refl
  not-or false false = refl

```
