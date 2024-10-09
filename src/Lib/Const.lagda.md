Lane Biocini
March 27st, 2024
revised Sept 4th, 2024 (added quote)

The empty type and the unit type. First, a quote from Hegel

```agda

{-# OPTIONS --safe #-}

module Lib.Const where

infix 3 ¬_
infix 3 ¬¬_
infix 3 ¬¬¬_

open import Prim.Universe

```

"The one thing needed to achieve scientific progress - and it is essential to
make an effort at gaining this quite simple insight into it - is the recognition
of the logical principle that negation is equally positive, or that what is
self-contradictory does not resolve itself into a nullity, into abstract
nothingness, but essentially only into the negation of its particular content;
or that such a negation is not just negation, but is the negation of the
determined fact which is resolved, and is therefore determinate negation; that
in the result there is contained in essence that from which the result derives -
a tautology indeed, since the result would otherwise be something immediate and
not a result. Because the result, the negation, is a determinate negation, it
has a content. It is a new concept but one higher and richer than the preceding
- richer because it negates or opposes the preceding and therefore contains it,
and it contains even more than that, for it is the unity of itself and its
opposite. It is above all in this way that the system of concepts is to be
erected, and it has come to completion in an unstoppable and pure progression
that admits of nothing extraneous."

Hegel, Science of Logic

```

data 𝟘 {u} : u type where

⊥ : Type
⊥ = 𝟘

elim : ∀ {u v} {A : v type} → 𝟘 {u} → A
elim = λ ()

syntax elim e = ex-falso e

contrapositive : ∀ {u v} {P : u type} {Q : v type}
     → (P → Q) → (Q → ⊥) → (P → ⊥)
contrapositive a nq p = nq (a p)

ind : ∀ {u v} (B : 𝟘 {u} → v type) → (e : 𝟘) → B e
ind A = λ ()

¬_ : ∀ {u} → u type → u type
¬ A = A → ⊥

¬¬_ : ∀ {u} → u type → u type
¬¬ A = ¬ (¬ A)

¬¬¬_ : ∀ {u} → u type → u type
¬¬¬ A = ¬ (¬ A)

record Uninhabited {u} (A : u type) : u type where
 field
  void : A → ⊥

open Uninhabited ⦃ ... ⦄ public

module _ {u} {A : u type} where
 instance
  null : {{¬ A}} → Uninhabited A
  null {{na}} .void = na

```

“This position could be suggested also for the benefit of those who are either
not comfortable, for whatever reason, with beginning with being and even less
with the transition into nothing that follows from being, or who simply do not
know how else to make a beginning in a science except by presupposing a
representation which is subsequently analyzed, the result of the analysis then
yielding the first determinate concept in the science. If we also want to test
this strategy, we must relinquish every particular object that we may intend,
since the beginning, as the beginning of thought, is meant to be entirely
abstract, entirely general, all form with no content; we must have nothing,
therefore, except the representation of a mere beginning as such. We have,
therefore, only to see what there is in this representation.”

Hegel, Science of Logic

```agda

record 𝟙 {u} : u type where instance constructor ⋆
open 𝟙 {{...}} public
{-# BUILTIN UNIT 𝟙 #-}

⊤ : Type
⊤ = 𝟙

unit-ind : ∀ {u} {P : ⊤ → u type}
    → P ⋆
    → (x : ⊤) → P x
unit-ind b = λ _ → b
