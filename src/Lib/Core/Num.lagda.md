Lane Biocini

```agda

{-# OPTIONS --safe --cubical-compatible --two-level #-}

module Lib.Num where

open import Lib.Core.Prim
open import Lib.Core.Type

open import Agda.Builtin.FromNat public
  renaming (Number to FromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to FromNeg)

record Num {u} (A : Type u) : Typeω where
  constructor MkNum
  infixl 8 _+_
  infixl 9 _*_

  field
    _+_ : A → A → A
    _*_ : A → A → A
    fromInteger : Int → A

open Num ⦃ ... ⦄ public
{-# INLINE MkNum #-}
{-# DISPLAY Num._+_ _ = _+_ #-}
{-# DISPLAY Num._*_ _ = _*_ #-}
{-# DISPLAY Num.fromInteger _ = fromInteger #-}

instance
  FromNat-Num : ∀ {u} {A : Type u} ⦃ N : Num A ⦄ → FromNat A
  FromNat-Num ⦃ N = N ⦄ .FromNat.Constraint = λ _ → Unit
  FromNat-Num ⦃ N = N ⦄ .FromNat.fromNat n = fromInteger ⦃ N ⦄ (pos n)

  Num-Int : Num Int
  Num-Int .Num._+_ = Int.add
  Num-Int .Num._*_ = Int.mul
  Num-Int .Num.fromInteger = λ x → x
  {-# INLINE Num-Int #-}

record Neg {u} (A : Type u) : Typeω where
  constructor MkNeg
  infix 10 negate
  infixl 8 _-_

  field
    ⦃ Num-Neg ⦄ : Num A
    negate : A → A
    _-_ : A → A → A

  subtract : A → A → A
  subtract = _-_

open Neg ⦃ ... ⦄ public
{-# INLINE MkNeg #-}
{-# DISPLAY Neg.negate _ = negate #-}
{-# DISPLAY Neg.subtract _ = subtract #-}
{-# DISPLAY Neg._-_ _ = _-_ #-}

instance
  FromNeg-Neg : ∀ {u} {A : Type u} ⦃ N : Neg A ⦄ → FromNeg A
  FromNeg-Neg ⦃ N = N ⦄ .FromNeg.Constraint = λ _ → Unit
  FromNeg-Neg ⦃ N = N ⦄ .FromNeg.fromNeg n = negate (fromInteger (pos n))
  {-# INLINE FromNeg-Neg #-}

  Neg-Int : Neg Int
  Neg-Int .Neg.Num-Neg = Num-Int
  Neg-Int .Neg.negate = Int.negate
  Neg-Int .Neg._-_ = Int.sub
  {-# INLINE Neg-Int #-}

record Abs {u} (A : Type u) : Typeω where
  constructor MkAbs
  field
    ⦃ Num-Abs ⦄ : Num A
    abs : A → A

open Abs ⦃ ... ⦄ public
{-# INLINE MkAbs #-}
{-# DISPLAY Abs.abs _ = abs #-}

record Fractional {u} (A : Type u) : Typeω where
  constructor MkFractional
  infixl 9 _/_
  field
    ⦃ Num-Fractional  ⦄ : Num A
    _/_ : A → A → A
    recip : A → A

open Fractional ⦃ ... ⦄ public
{-# INLINE MkFractional #-}
{-# DISPLAY Fractional._/_ _ = _/_ #-}
{-# DISPLAY Fractional.recip _ = recip #-}

record Integral {u} (A : Type u) : Typeω where
  constructor MkIntegral
  infixl 9 _div_ _mod_
  field
    ⦃ Num-Integral ⦄ : Num A
    _div_ : A → A → A
    _mod_ : A → A → A

open Integral ⦃ ... ⦄ public
{-# INLINE MkIntegral #-}
{-# DISPLAY Integral._div_ _ = _div_ #-}
{-# DISPLAY Integral._mod_ _ = _mod_ #-}
