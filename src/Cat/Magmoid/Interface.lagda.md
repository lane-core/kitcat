Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

open import Core.Type
open import Cat.Magmoid.Type

module Cat.Magmoid.Interface
  {adj : Level → Level → Level}
  (X : ∀ o h → magmoid-structure (adj o h) o h)
  where

import Cat.Magmoid.Base
import Cat.Magmoid.Map
import Cat.Magmoid.Het
import Cat.Magmoid.Nat

private
  M : ∀ o h C → Magmoids
  M o h C = magmoid-structure.to-magmoid (X o h) C

module base {o h} C = Cat.Magmoid.Base (M o h C)
module map {o o' h h'} C D = Cat.Magmoid.Map (M o h C) (M o' h' D)
module nat {o o' h h'} C D = Cat.Magmoid.Nat (M o h C) (M o' h' D)
module het {o o' h h'} C D = Cat.Magmoid.Het (M o h C) (M o' h' D)
