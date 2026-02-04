Character operations: predicates, case conversion, and encoding.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Prim.Char.Base where

open import Core.Type
open import Core.Prim.Char.Type

import Agda.Builtin.Char as C
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)

```

## Encoding

```agda

to-nat : Char → Nat
to-nat = C.primCharToNat
{-# INLINE to-nat #-}

from-nat : Nat → Char
from-nat = C.primNatToChar
{-# INLINE from-nat #-}

```

## Predicates

```agda

is-lower     : Char → Bool
is-lower = C.primIsLower
{-# INLINE is-lower #-}

is-digit     : Char → Bool
is-digit = C.primIsDigit
{-# INLINE is-digit #-}

is-alpha     : Char → Bool
is-alpha = C.primIsAlpha
{-# INLINE is-alpha #-}

is-space     : Char → Bool
is-space = C.primIsSpace
{-# INLINE is-space #-}

is-ascii     : Char → Bool
is-ascii = C.primIsAscii
{-# INLINE is-ascii #-}

is-latin1    : Char → Bool
is-latin1 = C.primIsLatin1
{-# INLINE is-latin1 #-}

is-print     : Char → Bool
is-print = C.primIsPrint
{-# INLINE is-print #-}

is-hex-digit : Char → Bool
is-hex-digit = C.primIsHexDigit
{-# INLINE is-hex-digit #-}

```

## Case conversion

```agda

to-upper : Char → Char
to-upper = C.primToUpper
{-# INLINE to-upper #-}

to-lower : Char → Char
to-lower = C.primToLower
{-# INLINE to-lower #-}

```

## Bool equality

```agda

char-eq : Char → Char → Bool
char-eq = C.primCharEquality
{-# INLINE char-eq #-}

```
