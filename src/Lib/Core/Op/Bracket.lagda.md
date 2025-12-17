This design pattern is lifted from 1Lab's version of this module, their
syntax notation for Sigma/Exists is very clever

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Api.Op.Bracket where

open import Lib.Core.Prim
open import Agda.Builtin.List

record Bracket {u} (A B : Type u) : Typeω where
  field
    [_] : A → B

open Bracket ⦃ ... ⦄ public
{-# DISPLAY Bracket.[_] _ X = [ X ] #-}

instance
  Bracket-Type : ∀ {u} → Bracket (Type u) (Type u)
  Bracket-Type .[_] A  = List A

  Bracket-List : ∀ {u} {A : Type u} → Bracket A (List A)
  Bracket-List .[_] x = x ∷ []
