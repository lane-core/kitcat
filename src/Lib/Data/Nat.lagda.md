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
open import Lib.Data.Unit using (⊤)

data Nat : u₀ type where
 zero : Nat
 suc : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

```

"We have now seen enough examples to get the general idea: when introducing a
new datatype, also define the generic fold operation for that datatype. When
the datatype is paramaterized, also introduce the appropriate mapping operation.
Given these functions, a number of other useful functions can be quickly defined."
- The Algebra of Programming, Section 1.4
  by Richard Bird and Oege de Moor

And that is how we'll proceed; in particular we'll include those useful functions
from their book.

```

induction : ∀ {u} (P : Nat → u type)
          → P zero
          → ((k : Nat) → P k → P (suc k))
          → (x : Nat) → P x
induction P c h zero = c
induction P c h (suc x) = h x (induction P c h x)

foldn : ∀ {u} {A : u type} → A → (A → A) → Nat → A
foldn c h zero = c
foldn c h (suc n) = h (foldn c h n)

```

We'll also define addition here, as it is useful for many applications so it's
good to have it as early as possible. Multiplication and Exonentiation as well.

```

add : Nat → Nat → Nat
add m = foldn m suc
{-# BUILTIN NATPLUS add #-}

mul : Nat → Nat → Nat
mul m = foldn zero (add m)
{-# BUILTIN NATTIMES mul #-}

expn : Nat → Nat → Nat
expn m = foldn 1 (mul m)

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
pattern matching. Notice also that its case trees are identical to monus in the
case that the right argument is greater or equal to the left. We'll take
advantage of this later.

```

dist : Nat → Nat → Nat
dist zero n = n
dist (suc m) zero = suc m
dist (suc m) (suc n) = dist m n

```

Here we have important elementary predicates, used to define our observational
equality and preorder, and serving to reify the possible cases in N.

```
is-zero : Nat → Type
is-zero zero = ⊤
is-zero (suc n) = ⊥

is-positive  : Nat → Type
is-positive zero = ⊥
is-positive (suc n) = ⊤

-- To maintain pred's totality, we will use is-positive as a predicate here
pred : ∀ n → is-positive n → Nat
pred zero = elim
pred (suc n) = λ _ → n
