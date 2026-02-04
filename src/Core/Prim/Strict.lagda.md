```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Prim.Strict where

open import Core.Type

open import Agda.Builtin.Strict public
  renaming (primForce to force; primForceLemma to force-lemma)

```