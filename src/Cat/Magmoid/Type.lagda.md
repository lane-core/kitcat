Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Magmoid.Type where

open import Core.Type

record Magmoids : Typeω where
  constructor str
  field
    {o h} : Level
    ob : Type o
    hom : ob → ob → Type h
    _⨾_ : ∀ {a b c} → hom a b → hom b c → hom a c
  infixr 40 _⨾_

{-# INLINE str #-}

record magmoid-structure v o h : Typeω where
  no-eta-equality
  field
    carrier : Type v
    ob : carrier → Type o
    hom : ∀ x → ob x → ob x → Type h
    cut : ∀ x {a b c} → hom x a b → hom x b c → hom x a c

  to-magmoid : carrier → Magmoids
  to-magmoid C .Magmoids.o = o
  to-magmoid C .Magmoids.h = h
  to-magmoid C .Magmoids.ob = ob C
  to-magmoid C .Magmoids.hom = hom C
  to-magmoid C .Magmoids._⨾_ = cut C
  {-# INLINE to-magmoid #-}

{-# INLINE magmoid-structure.constructor #-}
