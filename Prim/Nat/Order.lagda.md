Lane Biocini

Here we have a few varieties of defining natural number partial orders. First we
will consider the case of devising a hom over the unit type.

The case matching used by the traditional definition is the same that we use
for the distance function, where one branch of the case tree is defined to be
the empty type.

 _≤_ : Nat → Nat → Type
 _≤_ zero n = ⊤
 _≤_ (suc m) zero = ⊥
 _≤_ (suc m) (suc n) = dist m n

There are two properties that a partial order definition on Nat must satisfy, the
first being

We can find an algorithm that satisfies both, consider
our monus algorithm:

 sub : Nat → Nat → Nat
 sub zero n = zero
 sub (suc m) zero = suc m
 sub (suc m) (suc n) = sub m n.

Consider that we have two potential base cases specified by the case of the
first argument. we can consider what cases we want our partial order to have in
its definition. We know we will have the induction step no matter what, and this
step will resolve upon two possibilities. The induction step satisfies the
property we want for for the injectivity of the partial order, because if suc m
≤ suc n we have m ≤ n; naturally we want the base case to obtain when we recurse
to 0 ≤ x for some number x. The case where monus equals the left side of the
operator is zero,

```
module Prim.Nat.Order where

open import Prim.Universe
open import Prim.Nat

Nat-poset-unit : Nat → Nat → Type
Nat-poset-unit m n = is-zero (sub m n)

Nat-poset-idn : (m n : Nat) → Type
Nat-poset-idn m n = sub m n ≡ 0
 where open import Prim.Id using (_≡_)
