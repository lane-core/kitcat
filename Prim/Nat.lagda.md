Lane Biocini
March 27, 2024
revised August 4, 2024

Our beloved Natural Numbers. Maybe its this type that more than any others led
me to code this library, as many of the design choices I experimented with had
to do with my dissatisfaction at doing Number Theory while I was first learning
how to do Type Theory without conveniences like operator overloading and often
finding myself often having to duplicate work. For example moving from Natural
Numbers to Integers when we know that there should be some easy way to lift
lemmas from Nat to Int as the latter is the direct sum N ⊕ N with an
intersection at zero.

Much of my motivations for the design of this library thus came about from
wanting an ergonomic library for formalizing a wide variety of mathematics
without the mental overhead induced by managing an ever-expanding list of
symbols for which the prevalence of isomorphic structures in mathematics entails
that name conflicts are a structural inevitability. Therefore our treatment of
module syntax and semantics ought also to be systematic. If we should designate
things by the same name, even if symbols are slightly longer in character count
we benefit from a consistent module scheme for organizing data types and their
operations and properties, with notation type classes to provide consistent
interfaces for our mathematical work which also serve as guides for structuring
our formalizations.

The Natural Numbers can be described as perhaps the first 'trivially
non-trivial' ('non-trivially trivial' works just as well) object established in
base Martin-Lof Type Theory and mathematics generally. This is historical just
as much as it is conceptual, as Number theory has influenced the type of work
that organizes all fields of mathematical inquiry so pervasively that it is even
paradigmatic. Thus how a library organizes elementary number theory is
instructive for the overall attitude its design implements and ought to present
its most instructive example of the methods it will generally pursue in its
course of research.

```agda

{-# OPTIONS --safe #-}

module Prim.Nat where

open import Prim.Universe
open import Prim.Unit
open import Prim.Empty

empty-to-unit : ⊥ → ⊤
empty-to-unit _ = ⋆

empty-to-unit' : ⊥ → ⊤
empty-to-unit' e = ex-falso e

data Nat : Type where
 zero : Nat
 suc : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

induction : ∀ {𝓊} (P : Nat → 𝓊 type)
          → P zero
          → ((k : Nat) → P k → P (suc k))
          → (x : Nat) → P x
induction P b s zero = b
induction P b s (suc x) = s x (induction P b s x)

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

is-zero : Nat → Type
is-zero zero = ⊤
is-zero (suc n) = ⊥

is-positive  : Nat → Type
is-positive zero = ⊥
is-positive (suc n) = ⊤

```

We'll also define addition here, as it is useful for many applications so it's
good to have it as early as possible.

```

add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)
{-# BUILTIN NATPLUS add #-}

```

Likewise it is also useful to have the monus operator.

```

sub : Nat → Nat → Nat
sub zero n = zero
sub (suc m) zero = suc m
sub (suc m) (suc n) = sub m n
{-# BUILTIN NATMINUS sub #-}

```

The distance function, which can also be used for relations possible to define
on N. First and foremost we can use it to define the equality relation by
pattern matching. Notice also that its case trees are identical to monus save for
the case trees pertaining. We'll take advantage of this later.

```

dist : Nat → Nat → Nat
dist zero n = n
dist (suc m) zero = suc m
dist (suc m) (suc n) = dist m n

```

Typeclass for mapping integer numerals to elements of a type.

```

record Numeral {𝓊} (A : 𝓊 type) : 𝓊 ⁺ type where
 field
  is-pos : Nat → 𝓊 type
  from-nat : (n : Nat) {{_ : is-pos n}} → A

record NegNumeral {𝓊} (A : 𝓊 type) : 𝓊 ⁺ type where
 field
  is-neg : Nat → 𝓊 type
  from-nat : (n : Nat) {{_ : is-neg n}} → A

open Numeral ⦃ ... ⦄ using (is-pos) public
open NegNumeral ⦃ ... ⦄ using (is-neg) public

instance
 numeral-Nat : Numeral Nat
 numeral-Nat .is-pos = λ z → ⊥
 numeral-Nat .Numeral.from-nat = λ n ⦃ z ⦄ → n

{-# BUILTIN FROMNAT Numeral.from-nat #-}
{-# BUILTIN FROMNEG NegNumeral.from-nat #-}
