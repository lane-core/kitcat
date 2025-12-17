```agda

{-# OPTIONS --safe --erased-cubical #-}

module HData.Rack where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Kan
open import Lib.Equiv
open import Lib.Path
open import Lib.Sigma
open import Lib.Path.Gpd renaming (module cat to cat; cat to infixr 40 _∙_)
open import Lib.Pointed
open import Lib.Path.Homotopy

data R {u} (A : Type* u) : Type u where
  _∷_ : A .fst → R A → R A
  phi : ∀ xs → xs ≡ A .snd ∷ xs



private variable u : Level ; A : Type

