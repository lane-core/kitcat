Arithmetic operations on integers.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Int.Base where

open import Core.Type

open import Core.Data.Int.Type
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base using () renaming (_+_ to _+N_; _*_ to _*N_)

open import Agda.Builtin.Bool using (Bool; true; false)

module add where
  pos-negsuc : Nat → Nat → Int
  pos-negsuc Z     n     = negsuc n
  pos-negsuc (S m) Z     = pos m
  pos-negsuc (S m) (S n) = pos-negsuc m n
  {-# INLINE pos-negsuc #-}

zero : Int
zero = pos Z

negate : Int → Int
negate (pos Z)     = pos Z
negate (pos (S n)) = negsuc n
negate (negsuc n)  = pos (S n)
{-# INLINE negate #-}

add : Int → Int → Int
add (pos m)    (pos n)    = pos (m +N n)
add (pos m)    (negsuc n) = add.pos-negsuc m n
add (negsuc m) (pos n)    = add.pos-negsuc n m
add (negsuc m) (negsuc n) = negsuc (S (m +N n))
{-# INLINE add #-}

sub : Int → Int → Int
sub m n = add m (negate n)
{-# INLINE sub #-}

module mul where
  pos-negsuc : Nat → Nat → Int
  pos-negsuc Z     n = zero
  pos-negsuc (S m) n = negsuc (m +N (n +N (m *N n)))
  {-# INLINE pos-negsuc #-}

mul : Int → Int → Int
mul (pos m)    (pos n)    = pos (m *N n)
mul (pos m)    (negsuc n) = mul.pos-negsuc m n
mul (negsuc m) (pos n)    = mul.pos-negsuc n m
mul (negsuc m) (negsuc n) = pos (S (m +N (n +N (m *N n))))
{-# INLINE mul #-}

to-bool : Int → Bool
to-bool (pos Z)     = false
to-bool (pos (S n)) = true
to-bool (negsuc n)  = true
{-# INLINE to-bool #-}

to-nat : Int → Nat
to-nat (pos n)    = n
to-nat (negsuc n) = S n
{-# INLINE to-nat #-}

abs : Int → Int
abs m = pos (to-nat m)
{-# INLINE abs #-}

```
