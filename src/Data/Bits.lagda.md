Based on Tesla Zhang's "Two tricks to Trivialize Higher-Indexed Families" (2023)

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Bits where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Nat
open import Lib.Bool

record Bits {u} (A : Type u) : Type u where
  infixl 7 _&&_
  infixl 5 _||_
  field
    _&&_ : A -> A -> A             -- Bitwise AND
    _||_ : A -> A -> A             -- Bitwise OR
    xor : A -> A -> A              -- Bitwise XOR
    shiftL : A -> Nat -> A         -- Left shift
    shiftR : A -> Nat -> A         -- Right shift
    bit : Nat -> A                 -- Set nth bit
    zeroBits : A                   -- All bits zero
    oneBits : A
    complement : A -> A
    setBit : A -> Nat -> A         -- Set nth bit to 1
    testBit : A -> Nat -> Bool     -- Tests whether i-th bit is set

  complementBit : A -> Nat -> A
  complementBit x i = xor x (bit i)

  clearBit : A -> Nat -> A       -- Set nth bit to 0
  clearBit x i = x && complement (bit i)
