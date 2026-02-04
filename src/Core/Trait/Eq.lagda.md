Decidable equality trait (Idris2 style) and discrete types (HoTT-native).

The `Eq` trait provides Bool-returning equality for programming. The `Discrete`
trait provides Dec-returning equality for HoTT work, and implies `Eq`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Eq where

open import Core.Type
open import Core.Base
open import Core.Data.Bool
open import Core.Data.Dec
open Dec
open import Core.Data.Empty

private variable
  u : Level
  A : Type u

```

## Eq Trait

Bool-returning equality for programming, following Idris2 Prelude conventions.

```agda

record Eq {u} (A : Type u) : Type u where
  no-eta-equality
  infix 4 _==_ _/=_
  field
    _==_ : A → A → Bool

  _/=_ : A → A → Bool
  x /= y = Bool.not (x == y)

open Eq ⦃ ... ⦄ public
{-# INLINE Eq.constructor #-}

```

## Instances

```agda

private
  bool-eq : Bool → Bool → Bool
  bool-eq true true = true
  bool-eq true false = false
  bool-eq false true = false
  bool-eq false false = true

instance
  Eq-Bool : Eq Bool
  Eq-Bool ._==_ = bool-eq

  Eq-⊤ : Eq ⊤
  Eq-⊤ ._==_ _ _ = true

```

## Discrete Trait

HoTT-native decidable equality: returns `Dec (x ≡ y)` rather than `Bool`.

Discrete types are sets by Hedberg's theorem (proven in Core.Data.Dec).

```agda

record Discrete {u} (A : Type u) : Type u where
  no-eta-equality
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

  -- Derive Eq from Discrete
  discrete-eq : Eq A
  discrete-eq ._==_ x y with x ≟ y
  ... | yes _ = true
  ... | no  _ = false

open Discrete ⦃ ... ⦄ public
{-# INLINE Discrete.constructor #-}

-- Discrete implies is-set (via Hedberg)
Discrete→is-set : Discrete A → is-set A
Discrete→is-set d = hedberg (d .Discrete._≟_)

```

## Discrete Instances

```agda

instance
  Discrete-⊤ : Discrete ⊤
  Discrete-⊤ ._≟_ tt tt = yes refl

  Discrete-⊥ : Discrete ⊥
  Discrete-⊥ ._≟_ x = ex-falso x

```
