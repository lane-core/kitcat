Properties and proofs for the ternary finite set.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Data.Trie.Properties where

open import Core.Base
open import Core.Type
open import Core.Kan hiding (assoc)
open import Core.Transport
open import Core.Data.Dec
open Dec
open import Core.Data.Empty

open import Data.Trie.Type
open import Data.Trie.Base

```

## Decidable equality

Since `Trie` has exactly three nullary constructors, decidable equality
is nine ground cases: three diagonal (`yes refl`) and six off-diagonal
(discriminated via `subst`).

```agda

DecEq-Trie : (x y : Trie) → Dec (x ≡ y)
DecEq-Trie ll ll = yes refl
DecEq-Trie mm mm = yes refl
DecEq-Trie rr rr = yes refl
DecEq-Trie ll mm = no (λ p → subst f p tt) where f = λ { ll → ⊤ ; mm → ⊥ ; rr → ⊤ }
DecEq-Trie ll rr = no (λ p → subst f p tt) where f = λ { ll → ⊤ ; mm → ⊤ ; rr → ⊥ }
DecEq-Trie mm ll = no (λ p → subst f p tt) where f = λ { ll → ⊥ ; mm → ⊤ ; rr → ⊤ }
DecEq-Trie mm rr = no (λ p → subst f p tt) where f = λ { ll → ⊤ ; mm → ⊤ ; rr → ⊥ }
DecEq-Trie rr ll = no (λ p → subst f p tt) where f = λ { ll → ⊥ ; mm → ⊤ ; rr → ⊤ }
DecEq-Trie rr mm = no (λ p → subst f p tt) where f = λ { ll → ⊤ ; mm → ⊥ ; rr → ⊤ }

set : is-set Trie
set = hedberg DecEq-Trie

```

## Not

```agda

module not where
  period : ∀ t → not (not (not t)) ≡ t
  period ll = refl
  period mm = refl
  period rr = refl

```

## Flip

```agda

module flip where
  invol : ∀ t → flip (flip t) ≡ t
  invol ll = refl
  invol mm = refl
  invol rr = refl

```

## Min

```agda

module min where
  idem : ∀ t → min t t ≡ t
  idem ll = refl
  idem mm = refl
  idem rr = refl

  comm : ∀ a b → min a b ≡ min b a
  comm ll ll = refl
  comm ll mm = refl
  comm ll rr = refl
  comm mm ll = refl
  comm mm mm = refl
  comm mm rr = refl
  comm rr ll = refl
  comm rr mm = refl
  comm rr rr = refl

```

## Max

```agda

module max where
  idem : ∀ t → max t t ≡ t
  idem ll = refl
  idem mm = refl
  idem rr = refl

  comm : ∀ a b → max a b ≡ max b a
  comm ll ll = refl
  comm ll mm = refl
  comm ll rr = refl
  comm mm ll = refl
  comm mm mm = refl
  comm mm rr = refl
  comm rr ll = refl
  comm rr mm = refl
  comm rr rr = refl

```
