```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Core.Data.String where

open import Core.Type

import Agda.Builtin.String; module String = Agda.Builtin.String
  renaming ( primStringUncons to uncons
           ; primStringToList to to-list
           ; primStringFromList to from-list
           ; primStringAppend to append
           ; primStringEquality to Eq
           ; primShowChar to show-char
           ; primShowString to show-string
           ; primShowNat to show-nat
           )
open String using (String)

open import Agda.Builtin.FromString public
  renaming (IsString to FromString)

```