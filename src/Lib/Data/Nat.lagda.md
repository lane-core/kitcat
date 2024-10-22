Lane Biocini
March 27, 2024
revised August 4, 2024

"Forcing the programmer to write succ (succ (succ zero)) instead of 3, and to
re-create all of arithmetic from scratch would be a curious decision, to say
the least, by the designers of a programming language, so a standard syntax for
numbers is usally provided, so a standard syntax for numbers is usually provided,
as well as basic arithmetic operations."
- The Algebra of Programming, Section 1.2
  by Richard Bird and Oege de Moor

Our beloved Natural Numbers. Maybe its this type that more than any others that
led me to code this library, as many of the design choices I experimented with
had to do with my dissatisfaction at doing Number Theory while I was first
learning how to do Type Theory-- without conveniences like operator overloading
and often finductioning myself having to make accommodations for symbol name clashes,
and even duplicating work in other ways. For example, moving from Natural
Numbers to Integers when we know that there should be some easy way to lift
lemmas from Nat to Int as the latter is the direct sum N ⊕ N with an
intersection at zero.

Much of my motivations for the design of this library thus came about from
wanting an ergonomic library for formalizing a wide variety of mathematics
without the mental overhead inductionuced by managing an ever-expanding list of
symbols for which the prevalence of isomorphic structures in mathematics entails
name conflicts to form a structural inevitability. Therefore our treatment of
module syntax and semantics ought also to be systematic. If we should designate
things by the same name, even if symbols are slightly longer in character count
we benefit from a consistent module scheme for organizing data types and their
operations and properties, with notation type classes to provide consistent
interfaces for our mathematical work which also serve as guides for structuring
our formalizations.

Elementary Number theory, in both a historic and conceptual sense, has so
pervasively influenced the type of work that organizes all fields of
mathematical inquiry that it is even a paradigmatic case; just think how we
still memorize Euclid in grade school. We might consider then that how a library
organizes elementary number theory is instructive for the overall attitude it
implements, and it ought to present an elementary and instructive example of the
type of code contained therein.

```agda

{-# OPTIONS --safe #-}

module Lib.Data.Nat where

open import Lib.Prim
open import Lib.Data.Empty
open import Lib.Data.Unit

data Nat : u₀ type where
 zero : Nat
 suc : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}
