```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Cat.Base where

open import Lib.Type
open import Lib.Builtin
open import Lib.Path
open import Lib.Graph
open import Lib.Graph.Virtual
open import Lib.Cut
import Lib.Graph.Arrow

record is-category {u v} (G : Graph u v) : Type (u ⊔ v ₊) where
  private
    Ob = Graph.₀ G
    _~>_ = Graph.₁ G
    infix 4 _~>_

  field
    vequ : virtual-equipment G

  open virtual-equipment vequ renaming (Htpy to infix 4 _≈_; concat to infixr 40 _·_)
  private module C = Lib.Graph.Arrow (G , vequ)
  field
    unital : ∀ x → C.is-unital x
    comp : C.is-composable
    assoc : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z)
          → (f · g) · h ≈ f · g · h

record Category u v : Type₊ (u ⊔ v) where
  constructor category
  field
    graph : Graph u v
    axioms : is-category graph

  private module C = is-category axioms
  private module Arr = Lib.Graph.Arrow (graph , C.vequ)
  private module unit {x} = Arr.unital (C.unital x)

  Ob : Type u
  Ob = Graph.₀ graph

  _~>_ : Ob → Ob → Type v
  _~>_ = Graph.₁ graph

  _≈_ : ∀ {x y} → x ~> y → x ~> y → Type v
  _≈_ = virtual-equipment.Htpy C.vequ

  instance
    Cut-Category : Hom-cut _~>_
    Cut-Category .Cut.seq = virtual-equipment.concat C.vequ

    dCut-Category : dHom-cut _~>_ _≈_
    dCut-Category .dCut.dCut-cut = Cut-Category
    dCut-Category .dCut.hconcat = virtual-equipment.hconcat C.vequ

    vCut-Category : ∀ {x y} → Hom-cut-alt (_≈_ {x} {y})
    vCut-Category .Cut-alt.seq = virtual-equipment.vconcat C.vequ

  idn : ∀ {x} → x ~> x
  idn {x} = unit.idn

  heqv : ∀ {x y} {f : x ~> y} → f ≈ f
  heqv = virtual-equipment.heqv C.vequ

  module path where
    unitl : ∀ {x y} (f : x ~> y) → idn ∙ f ＝ f
    unitl = unit.unitl-comp

    unitr : ∀ {x y} (f : x ~> y) → f ∙ idn ＝ f
    unitr = unit.unitr-comp

    assoc : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z)
          → (f ∙ g) ∙ h ＝ f ∙ g ∙ h
    assoc f g h = cong fst pf where
      pf : ((f ∙ g) ∙ h , heqv) ＝ (f ∙ g ∙ h , C.assoc f g h)
      pf = Arr.is-composable.assoc-paths C.comp f g h (f ∙ g ∙ h , C.assoc f g h)

  unitl : ∀ {x y} (f : x ~> y) → idn ∙ f ≈ f
  unitl = unit.unitl

  unitr : ∀ {x y} (f : x ~> y) → f ∙ idn ≈ f
  unitr = unit.unitr

  assoc : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z) → (f ∙ g) ∙ h ≈ f ∙ g ∙ h
  assoc = C.assoc
