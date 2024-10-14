Lane Biocini
March 27st, 2024
revised Sept 4th, 2024 (added quote)

First, a quote:

> The one thing needed to achieve scientific progress - and it is essential to
> make an effort at gaining this quite simple insight into it - is the recognition
> of the logical principle that negation is equally positive, or that what is
> self-contradictory does not resolve itself into a nullity, into abstract
> nothingness, but essentially only into the negation of its particular content;
> or that such a negation is not just negation, but is the negation of the
> determined fact which is resolved, and is therefore determinate negation; that
> in the result there is contained in essence that from which the result derives -
> a tautology indeed, since the result would otherwise be something immediate and
> not a result. Because the result, the negation, is a determinate negation, it
> has a content. It is a new concept but one higher and richer than the preceding
> - richer because it negates or opposes the preceding and therefore contains it,
> and it contains even more than that, for it is the unity of itself and its
> opposite. It is above all in this way that the system of concepts is to be
> erected, and it has come to completion in an unstoppable and pure progression
> that admits of nothing extraneous.

Hegel, Science of Logic

```agda

{-# OPTIONS --safe #-}

module Lib.Negation where

infix 3 ¬_
infix 3 ¬¬_
infix 3 ¬¬¬_

open import Lib.Prim
open import Lib.Data.Empty using (𝟘; ⊥)

contrapositive : ∀ {u v} {P : u type} {Q : v type}
     → (P → Q) → (Q → ⊥) → (P → ⊥)
contrapositive a nq p = nq (a p)

¬_ : ∀ {u} → u type → u type
¬ A = A → ⊥

¬¬_ : ∀ {u} → u type → u type
¬¬ A = ¬ (¬ A)

¬¬¬_ : ∀ {u} → u type → u type
¬¬¬ A = ¬ (¬ A)
