Lane Biocini
Oct 13th, 2024

From Rijke's Introduction to Homotopy Type Theory, but this construction is
heavily borrowed from Jon Sterling's implementation in the TypeTopology module
UF.IdentitySystem.

We also lean on 1lab's formalization of this concept, with some tweaks of course

```

{-# OPTIONS --safe #-}

module Lib.Trait.Numeral where

open import Lib.Prim
open import Lib.Rel
open import Lib.Data.Nat
open import Lib.Trait.IdSys.Type public

```

Typeclass for mapping integer numerals to elements of a type.

```

record Numeral {u} (A : u type) : u ⁺ type where
 field
  is-pos : Nat → u type
  from-nat : (n : Nat) {{_ : is-pos n}} → A

record NegNumeral {u} (A : u type) : u ⁺ type where
 field
  is-neg : Nat → u type
  from-nat : (n : Nat) {{_ : is-neg n}} → A

open Numeral ⦃ ... ⦄ using (is-pos) public
open NegNumeral ⦃ ... ⦄ using (is-neg) public

instance
 numeral-Nat : Numeral Nat
 numeral-Nat .is-pos = λ z → ⊥
 numeral-Nat .Numeral.from-nat = λ n ⦃ z ⦄ → n

{-# BUILTIN FROMNAT Numeral.from-nat #-}
{-# BUILTIN FROMNEG NegNumeral.from-nat #-}
