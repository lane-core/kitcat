Interval-based function extensionality.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Interval where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport

private variable ℓ : Level

open Core.Kan using (conn) public

open Core.Base using (funext; happly) public

open Core.Kan using (_∙_; unitl; unitr; invl; invr; assoc) public
open Core.Base using (sym) public

```
