Float operations: arithmetic, trigonometry, predicates, and conversions.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Prim.Float.Base where

open import Core.Type
open import Core.Prim.Float.Type

import Agda.Builtin.Float as F
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Word using (Word64)

```

## Arithmetic

```agda

infixl 6 _+_ _-_
infixl 7 _*_ _/_

_+_ : Float → Float → Float
_+_ = F.primFloatPlus
{-# INLINE _+_ #-}

_-_ : Float → Float → Float
_-_ = F.primFloatMinus
{-# INLINE _-_ #-}

_*_ : Float → Float → Float
_*_ = F.primFloatTimes
{-# INLINE _*_ #-}

_/_ : Float → Float → Float
_/_ = F.primFloatDiv
{-# INLINE _/_ #-}

_^_ : Float → Float → Float
_^_ = F.primFloatPow
{-# INLINE _^_ #-}

negate : Float → Float
negate = F.primFloatNegate
{-# INLINE negate #-}

sqrt : Float → Float
sqrt = F.primFloatSqrt
{-# INLINE sqrt #-}

exp : Float → Float
exp = F.primFloatExp
{-# INLINE exp #-}

log : Float → Float
log = F.primFloatLog
{-# INLINE log #-}

```

## Trigonometry

```agda

sin   : Float → Float
sin = F.primFloatSin
{-# INLINE sin #-}

cos   : Float → Float
cos = F.primFloatCos
{-# INLINE cos #-}

tan   : Float → Float
tan = F.primFloatTan
{-# INLINE tan #-}

asin  : Float → Float
asin = F.primFloatASin
{-# INLINE asin #-}

acos  : Float → Float
acos = F.primFloatACos
{-# INLINE acos #-}

atan  : Float → Float
atan = F.primFloatATan
{-# INLINE atan #-}

atan2 : Float → Float → Float
atan2 = F.primFloatATan2
{-# INLINE atan2 #-}

sinh  : Float → Float
sinh = F.primFloatSinh
{-# INLINE sinh #-}

cosh  : Float → Float
cosh = F.primFloatCosh
{-# INLINE cosh #-}

tanh  : Float → Float
tanh = F.primFloatTanh
{-# INLINE tanh #-}

asinh : Float → Float
asinh = F.primFloatASinh
{-# INLINE asinh #-}

acosh : Float → Float
acosh = F.primFloatACosh
{-# INLINE acosh #-}

atanh : Float → Float
atanh = F.primFloatATanh
{-# INLINE atanh #-}

```

## Predicates

```agda

is-infinite     : Float → Bool
is-infinite = F.primFloatIsInfinite
{-# INLINE is-infinite #-}

is-nan          : Float → Bool
is-nan = F.primFloatIsNaN
{-# INLINE is-nan #-}

is-negative-zero : Float → Bool
is-negative-zero = F.primFloatIsNegativeZero
{-# INLINE is-negative-zero #-}

is-safe-integer : Float → Bool
is-safe-integer = F.primFloatIsSafeInteger
{-# INLINE is-safe-integer #-}

```

## Comparison

```agda

float-eq   : Float → Float → Bool
float-eq = F.primFloatEquality
{-# INLINE float-eq #-}

float-ineq : Float → Float → Bool
float-ineq = F.primFloatInequality
{-# INLINE float-ineq #-}

float-less : Float → Float → Bool
float-less = F.primFloatLess
{-# INLINE float-less #-}

```

## Conversions

```agda

from-nat   : Nat → Float
from-nat = F.primNatToFloat
{-# INLINE from-nat #-}

from-int   : Int → Float
from-int = F.primIntToFloat
{-# INLINE from-int #-}

round      : Float → Maybe Int
round = F.primFloatRound
{-# INLINE round #-}

floor      : Float → Maybe Int
floor = F.primFloatFloor
{-# INLINE floor #-}

ceiling    : Float → Maybe Int
ceiling = F.primFloatCeiling
{-# INLINE ceiling #-}

to-ratio   : Float → Σ Int (λ _ → Int)
to-ratio = F.primFloatToRatio
{-# INLINE to-ratio #-}

from-ratio : Int → Int → Float
from-ratio = F.primRatioToFloat
{-# INLINE from-ratio #-}

decode     : Float → Maybe (Σ Int λ _ → Int)
decode = F.primFloatDecode
{-# INLINE decode #-}

encode     : Int → Int → Maybe Float
encode = F.primFloatEncode
{-# INLINE encode #-}

to-word64  : Float → Maybe Word64
to-word64 = F.primFloatToWord64
{-# INLINE to-word64 #-}

show-float : Float → String
show-float = F.primShowFloat
{-# INLINE show-float #-}

```
