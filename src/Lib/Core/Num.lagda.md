Lane Biocini

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Num where

open import Lib.Core.Prim

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.FromNat public
  renaming (Number to FromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to FromNeg)

module Nat where
  open import Agda.Builtin.Nat public
    using (Nat; _+_; _*_)
    renaming ( zero to Zero
             ; suc to Suc
             ; _-_ to _∸_
             ; _==_ to Eq )
    hiding (module Nat)

  data _<_ (m : Nat) : Nat → Type where
    Base : m < Suc m
    Step : ∀ {n} → m < n → m < Suc n

  module _ where
    open import Agda.Builtin.Cubical.Path

    +runit : ∀ n → n + Zero ≡ n
    +runit Zero i = Zero
    +runit (Suc n) i = Suc (+runit n i)

    +assoc : ∀ m n k → (m + n) + k ≡ m + (n + k)
    +assoc m Zero k i = +runit m i + k
    +assoc Zero (Suc n) k i = Suc (n + k)
    +assoc (Suc m) (Suc n) k i = Suc (+assoc m (Suc n) k i)

open Nat public using (Nat)

pattern Z = Nat.Zero
pattern S n = Nat.Suc n

module Int where
  open import Agda.Builtin.Int public hiding (module Int)
  open Agda.Builtin.Int.Int public

  module add where
    pos-negsuc : Nat → Nat → Int
    pos-negsuc Z n = negsuc n
    pos-negsuc (S m) Z = pos m
    pos-negsuc (S m) (S n) = pos-negsuc m n
    {-# INLINE pos-negsuc #-}

  zero : Int
  zero = pos Z

  negate : Int → Int
  negate (pos Z) = pos Z
  negate (pos (S n)) = negsuc n
  negate (negsuc n) = pos (S n)
  {-# INLINE negate #-}

  add : Int → Int → Int
  add (pos m) (pos n) = pos (Nat._+_ m n)
  add (pos m) (negsuc n) = add.pos-negsuc m n
  add (negsuc m) (pos n) = add.pos-negsuc n m
  add (negsuc m) (negsuc n) = negsuc (S (Nat._+_ m n))
  {-# INLINE add #-}

  sub : Int → Int → Int
  sub m = λ n → add m (negate n)

  module mul where
    pos-negsuc : Nat → Nat → Int
    pos-negsuc Z n = zero
    pos-negsuc (S m) n = negsuc (Nat._+_ m (Nat._+_ n (Nat._*_ m n)))
    {-# INLINE pos-negsuc #-}

  mul : Int → Int → Int
  mul (pos m) (pos n) = pos (Nat._*_ m n)
  mul (pos m) (negsuc n) = mul.pos-negsuc m n
  mul (negsuc m) (pos n) = mul.pos-negsuc n m
  mul (negsuc m) (negsuc n) = pos (S (Nat._+_ m (Nat._+_ n (Nat._*_ m n))))
  {-# INLINE mul #-}

  to-bool : Int → Bool
  to-bool (pos Z) = false
  to-bool (pos (S n)) = true
  to-bool (negsuc n) = true
  {-# INLINE to-bool #-}

  to-nat : Int → Nat
  to-nat (pos n) = n
  to-nat (negsuc n) = S n
  {-# INLINE to-nat #-}

  abs : Int → Int
  abs m = pos (to-nat m)
  {-# INLINE abs #-}

open Int public using (Int; pos; negsuc)

record Num {u} (A : Type u) : Typeω where
  constructor MkNum
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
{-# INLINE MkNum #-}
{-# DISPLAY Num._+_ _ = _+_ #-}
{-# DISPLAY Num._*_ _ = _*_ #-}
{-# DISPLAY Num.fromInteger _ = fromInteger #-}
{-# DISPLAY Nat._+_ = _+_ #-}

instance
  Num-Nat : Num Nat
  Num-Nat ._+_ = Nat._+_
  Num-Nat ._*_ = Nat._*_
  Num-Nat .fromInteger = Int.to-nat

  Num-Int : Num Int
  Num-Int ._+_ = Int.add
  Num-Int ._*_ = Int.mul
  Num-Int .fromInteger = λ x → x
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

  instance
    FromNeg-Neg : FromNeg A
    FromNeg-Neg .FromNeg.Constraint = λ _ → Lift u ⊤
    FromNeg-Neg .FromNeg.fromNeg n = negate (fromInteger (pos n))
    {-# INLINE FromNeg-Neg #-}

instance
   Neg-Int : Neg Int
   Neg-Int .Neg.Num-Neg = Num-Int
   Neg-Int .Neg.negate = Int.negate
   Neg-Int .Neg._-_ = Int.sub
   {-# INLINE Neg-Int #-}

open Neg ⦃ ... ⦄ public
{-# INLINE MkNeg #-}
{-# DISPLAY Neg.negate _ = negate #-}
{-# DISPLAY Neg.subtract _ = subtract #-}
{-# DISPLAY Neg._-_ _ = _-_ #-}

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
