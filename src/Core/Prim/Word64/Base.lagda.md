Word64 operations: encoding to and from natural numbers.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Prim.Word64.Base where

open import Core.Prim.Word64.Type

import Agda.Builtin.Word as W
open import Agda.Builtin.Nat using (Nat)

to-nat : Word64 → Nat
to-nat = W.primWord64ToNat
{-# INLINE to-nat #-}

from-nat : Nat → Word64
from-nat = W.primWord64FromNat
{-# INLINE from-nat #-}

```
