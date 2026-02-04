The Graphical typeclass for graph-like structures.

A type is `Graphical` when it has an underlying graph structure consisting of
vertices and edges. This abstracts over categories, semicategories, typoids,
and other structures that share this common shape.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Graphical where

open import Core.Type

```

## Graphical trait

The `Graphical` record captures the essential interface: given a structure `x`,
we can extract its type of vertices `∣ x ∣` and its family of edge types
`x [ a ~> b ]`. The universe levels for vertices and edges are implicit fields.

```agda

record Graphical {u} (A : Type u) : Typeω where
  field
    {v e} : Level
    ∣_∣ : A → Type v
    _[_~>_] : ∀ x → ∣ x ∣ → ∣ x ∣ → Type e
  {-# INLINE ∣_∣ #-}
  {-# INLINE _[_~>_] #-}

open Graphical ⦃ ... ⦄ using (∣_∣; _[_~>_]) public

```

## Helper functions

These utilities provide convenient syntax for working with graphical structures.

```agda

module _ {u} {C : Type u} ⦃ G : Graphical C ⦄ where
  private module M = Graphical G

  edge-syntax : (c : C) → M.∣ c ∣ → M.∣ c ∣ → Type (Graphical.e G)
  edge-syntax c = Graphical._[_~>_] G c
  syntax edge-syntax C x y = x ~> y ∶ C

  ob : (c : C) → Type (Graphical.v G)
  ob c = M.∣ c ∣

```
