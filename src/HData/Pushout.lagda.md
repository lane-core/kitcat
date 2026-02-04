Pushouts as a higher inductive type.

The pushout of two maps `f : C -> A` and `g : C -> B` is the universal
cocone. Geometrically, a pushout glues `A` and `B` together along their
common preimage `C`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Pushout where

open import HData.Pushout.Type public hiding (module Pushout)

module Pushout where
  open import HData.Pushout.Base public

module Susp where
  open import HData.Pushout.Suspension public

module Join where
  open import HData.Pushout.Join public

module Pushout-properties where
  open import HData.Pushout.Properties public
```
