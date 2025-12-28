```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

import Lib.Graph.Reflexive.Base
import Lib.Graph.Reflexive.Displayed

module Lib.Graph.Reflexive.Fibration {u v w z}
  (R : Lib.Graph.Reflexive.Base.Rx u v)
  (D : Lib.Graph.Reflexive.Displayed.Disp-rx R w z)
  where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Type
open import Lib.Graph.Reflexive.Displayed R
open Lib.Graph.Reflexive.Base

open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)
open Lib.Graph.Reflexive.Displayed.Disp-rx D
  renaming (vtx to V; ₂ to E)

