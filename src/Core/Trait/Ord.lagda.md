Total ordering trait following Idris2 Prelude conventions, with heavy influence
from the agda-prelude library.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Ord where

open import Core.Type
open import Core.Base
open import Core.Data.Bool
open import Core.Trait.Eq

private variable
  u : Level
  A : Type u

```

## Ordering Type

```agda

data Comparison {a} {A : Type a} (_<_ : A → A → Type a) (x y : A) : Type a where
  less    : (lt : x < y) → Comparison _<_ x y
  equal   : (eq : x ≡ y) → Comparison _<_ x y
  greater : (gt : y < x) → Comparison _<_ x y

is-less : ∀ {a} {A : Type a} {R : A → A → Type a} {x y} → Comparison R x y → Bool
is-less (less    _) = true
is-less (equal   _) = false
is-less (greater _) = false
{-# INLINE is-less #-}

is-greater : ∀ {a} {A : Type a} {R : A → A → Type a} {x y} → Comparison R x y → Bool
is-greater (less    _) = false
is-greater (equal   _) = false
is-greater (greater _) = true

infixr 0 comparison-elim
syntax comparison-elim c (λ l → x) (λ e → y) (λ g → z) =
  cmp c
    lt: l => x
    eq: e => y
    gt: g => z

-- The termination checker can't handle merge-like functions using 'with'.
-- Use this instead. -- from agda-prelude
comparison-elim
  : ∀ {u v} {A : Type u} {B : Type v} {_<_ : A → A → Type u} {x y : A}
  → Comparison _<_ x y
  → (x < y → B)
  → (x ≡ y → B)
  → (y < x → B)
  → B
comparison-elim (less    p) lt eq gt = lt p
comparison-elim (equal   p) lt eq gt = eq p
comparison-elim (greater p) lt eq gt = gt p
{-# INLINE comparison-elim #-}


```

```
