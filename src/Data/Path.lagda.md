```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Path where

open import Lib.Core.Prim

import Lib.Core.Kan; module Kan = Lib.Core.Kan hiding (transp)
import Lib.Path.HLevel; module HLevel = Lib.Path.HLevel
open import Lib.Core.Base public
open import Lib.Path public
open import Lib.Path.Gpd public


open Path
  using ( Path
        ; rfl
        ; hsym
        ; ap
        ; tr
        ; idtofun
        ; funext
        ; happly
        ; J
        ; fiber
        ; is-contr
        ; is-prop
        ; is-set
        )
  public

Own : ∀ {u} {A : Type u} → A → A → Type u
Own a = λ x → x ≡ a

