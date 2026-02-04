Numeric type class for literal overloading.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Num where

open import Core.Type
open import Core.Data.Nat.Type
import Core.Data.Nat.Base as Nat
open import Core.Data.Int public
open Int hiding (negate; abs)

open import Agda.Builtin.Unit
open import Agda.Builtin.FromNat public
  renaming (Number to FromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to FromNeg)

record Num {u} (A : Type u) : Typeω where
  infixl 8 _+_
  infixl 9 _*_

  field
    _+_ : A → A → A
    _*_ : A → A → A
    fromInteger : Int → A

  instance
    FromNat-Num : FromNat A
    FromNat-Num .FromNat.Constraint Z = Lift u ⊤
    FromNat-Num .FromNat.Constraint (S n) = Lift u ⊤
    FromNat-Num .FromNat.fromNat n = fromInteger (pos n)

open Num ⦃ ... ⦄ public
{-# DISPLAY Num._+_ _ = _+_ #-}
{-# DISPLAY Num._*_ _ = _*_ #-}
{-# DISPLAY Num.fromInteger _ = fromInteger #-}
{-# DISPLAY Nat._+_ = _+_ #-}

instance
  Num-Int : Num Int
  Num-Int ._+_ = add
  Num-Int ._*_ = mul
  Num-Int .fromInteger = λ x → x
  {-# INLINE Num-Int #-}

record Neg {u} (A : Type u) : Typeω where
  infix 10 negate
  infixl 8 _-_

  field
    ⦃ Num-Neg ⦄ : Num A
    negate : A → A
    _-_ : A → A → A

  subtract : A → A → A
  subtract = _-_

  instance
    FromNeg-Neg : FromNeg A
    FromNeg-Neg .FromNeg.Constraint = λ _ → Lift u ⊤
    FromNeg-Neg .FromNeg.fromNeg n = negate (fromInteger (pos n))
    {-# INLINE FromNeg-Neg #-}

instance
  Neg-Int : Neg Int
  Neg-Int .Neg.Num-Neg = Num-Int
  Neg-Int .Neg.negate = Int.negate
  Neg-Int .Neg._-_ = sub
  {-# INLINE Neg-Int #-}

open Neg ⦃ ... ⦄ public
{-# DISPLAY Neg.negate _ = negate #-}
{-# DISPLAY Neg.subtract _ = subtract #-}
{-# DISPLAY Neg._-_ _ = _-_ #-}

record Abs {u} (A : Type u) : Typeω where
  field
    ⦃ Num-Abs ⦄ : Num A
    abs : A → A

open Abs ⦃ ... ⦄ public
{-# DISPLAY Abs.abs _ = abs #-}

record Fractional {u} (A : Type u) : Typeω where
  infixl 9 _/_
  field
    ⦃ Num-Fractional ⦄ : Num A
    _/_ : A → A → A
    recip : A → A

open Fractional ⦃ ... ⦄ public
{-# DISPLAY Fractional._/_ _ = _/_ #-}
{-# DISPLAY Fractional.recip _ = recip #-}

record Integral {u} (A : Type u) : Typeω where
  infixl 9 _div_ _mod_
  field
    ⦃ Num-Integral ⦄ : Num A
    _div_ : A → A → A
    _mod_ : A → A → A

open Integral ⦃ ... ⦄ public
{-# DISPLAY Integral._div_ _ = _div_ #-}
{-# DISPLAY Integral._mod_ _ = _mod_ #-}

```
