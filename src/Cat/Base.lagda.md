```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Cat.Base where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Core.Kan
open import Lib.Path
open import Lib.Equal
open import Lib.Graph
open import Lib.Graph.Virtual
open import Lib.Core.Cut
import Lib.Graph.Arrow

record is-category {u v} (G : Graph u v) : Type (u ⊔ v ₊) where
  private
    Ob = Graph.₀ G
    _~>_ = Graph.₁ G
    infix 4 _~>_

  field
    _≈_ : ∀ {x y} → x ~> y → x ~> y → Type v
    heqv : ∀ {x y} {f : x ~> y} → f ≈ f

  vequ : virtual-equipment G
  vequ = ?

  open virtual-equipment vequ renaming (Htpy to infix 4 _≈_; concat to infixr 40 _·_)
  private module C = Lib.Graph.Arrow (G , vequ)
  field
    unital : ∀ x → C.is-unital x
    composable : C.is-composable
    assoc : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z)
          → (f · g) · h ≈ f · g · h

  comp-prop : ∀ {x y z} (f : Graph.₁ G x y) (g : Graph.₁ G y z) → is-prop (C.has-path f g)
  comp-prop = C.is-composable.comp-prop composable

record Category u v : Type₊ (u ⊔ v) where
  field
    graph : Graph u v
    axioms : is-category graph

  private module C = is-category axioms
  private module V = virtual-equipment C.vequ
  private module Arr = Lib.Graph.Arrow (graph , C.vequ)
  private module unit {x} = Arr.unital (C.unital x)

  vgraph : Virtual-graph u v
  vgraph = graph , C.vequ

  unital : ∀ x → Arr.is-unital x
  unital x = C.unital x

  Ob : Type u
  Ob = Graph.₀ graph

  _~>_ : Ob → Ob → Type v
  _~>_ = Graph.₁ graph

  _≈_ : ∀ {x y} → x ~> y → x ~> y → Type v
  _≈_ = V.Htpy

  idn : ∀ {x} → x ~> x
  idn {x} = unit.idn

  heqv : ∀ {x y} {f : x ~> y} → f ≈ f
  heqv = V.heqv

  hsym : ∀ {x y} {f g : x ~> y} → f ≈ g → g ≈ f
  hsym = V.hsym

  vconcat : ∀ {x y} {f g h : x ~> y} → f ≈ g → g ≈ h → f ≈ h
  vconcat = V.vconcat

  instance
    Cut-Category : Hom-cut _~>_
    Cut-Category .Cut.seq = V.concat

    dCut-Category : dHom-cut _~>_ _≈_
    dCut-Category .dCut.dCut-cut = Cut-Category
    dCut-Category .dCut.hconcat = V.hconcat

    vCut-Category : ∀ {x y} → Hom-cut-alt (_≈_ {x} {y})
    vCut-Category .Cut-alt.seq = V.vconcat

  hconcat : ∀ {x y z} {f1 f2 : x ~> y} {g1 g2 : y ~> z}
          → f1 ≈ f2 → g1 ≈ g2 → f1 ∙ g1 ≈ f2 ∙ g2
  hconcat = V.hconcat

  comp-prop : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-prop (Arr.has-path f g)
  comp-prop = C.comp-prop

  comp-contr : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-contr (Arr.has-path f g)
  comp-contr f g = Arr.is-composable.comp-contr C.composable f g

  hpath : ∀ {x y} {f g : x ~> y} (h : f ≈ g)
              → (f , unit.unitr g ⨾ hsym h) ＝ (g , unit.unitr g)
  hpath {f} {g} h = C.comp-prop g idn (f , unit.unitr g ⨾ hsym h) (g , unit.unitr g)

  eqtopath : ∀ {x y} {f g : x ~> y} (h : f ≈ g) → f ＝ g
  eqtopath h = cong fst (hpath h)

  eqtopathp : ∀ {x y} {f g : x ~> y} (h : f ≈ g)
           → PathP (λ i → g ∙ idn ≈ eqtopath h i) (unit.unitr g ⨾ hsym h) (unit.unitr g)
  eqtopathp h = ap snd (hpath h)

  module path where
    unitl : ∀ {x y} (f : x ~> y) → idn ∙ f ＝ f
    unitl = unit.unitl-comp

    unitr : ∀ {x y} (f : x ~> y) → f ∙ idn ＝ f
    unitr = unit.unitr-comp

    assoc : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z)
          → (f ∙ g) ∙ h ＝ f ∙ g ∙ h
    assoc f g h = cong fst path where
      path = comp-prop f (g ∙ h) ((f ∙ g) ∙ h , hsym (C.assoc f g h)) ((f ∙ g ∙ h) , heqv)

  unitl : ∀ {x y} (f : x ~> y) → idn ∙ f ≈ f
  unitl = unit.unitl

  unitr : ∀ {x y} (f : x ~> y) → f ∙ idn ≈ f
  unitr = unit.unitr

  assoc : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z) → (f ∙ g) ∙ h ≈ f ∙ g ∙ h
  assoc = C.assoc

  eqtopath-heqv : ∀ {x y} {f : x ~> y} → eqtopath (heqv {f = f}) ＝ refl
  eqtopath-heqv = {!!}
```
module Cat {u v} (C : Category u v) where
  open Category C
  module arrow = Lib.Graph.Arrow vgraph
  module unit {x} = arrow.unital (unital x)

  op : Category u v
  op .graph = Graph.op graph
  op .axioms .is-category.vequ .virtual-equipment.Htpy = _≈_
  op .axioms .is-category.vequ .virtual-equipment.concat f g = g ∙ f
  op .axioms .is-category.vequ .virtual-equipment.heqv = heqv
  op .axioms .is-category.vequ .virtual-equipment.hsym = hsym
  op .axioms .is-category.vequ .virtual-equipment.vconcat = vconcat
  op .axioms .is-category.vequ .virtual-equipment.hconcat H K = hconcat K H
  op .axioms .is-category.unital x .arrow.is-unital.idn = idn
  op .axioms .is-category.unital x .arrow.is-unital.iso .arrow.is-cocartesian.left =
    arrow.unital.right-cocartesian (unital x)
  op .axioms .is-category.unital x .arrow.is-unital.iso .arrow.is-cocartesian.right =
    arrow.unital.left-cocartesian (unital x)
  op .axioms .is-category.unital x .arrow.is-unital.thk = unit.is-lin
  op .axioms .is-category.unital x .arrow.is-unital.lin = unit.is-thk
  op .axioms .is-category.composable .arrow.is-composable.comp-prop f g = comp-prop g f
  op .axioms .is-category.assoc f g h = hsym (assoc h g f)



module Typd {u v} (C : Category u v) where
  open Category C
  open Lib.Graph.Arrow vgraph

  eq-to-path-refl : ∀ {x y} (f : x ~> y) → eqtopath (heqv {f = f}) ＝ refl
  eq-to-path-refl f = {!cong fst (hpath ?)!} where
    -- hpath heqv : (g , unitr g ⨾ hsym heqv) ＝ (g , unitr g)
    -- But we know unitr g ⨾ hsym heqv ＝ unitr g from step 2

    canonical : (f , unitr f ∙ hsym heqv) ＝ (f , unitr f)
    canonical = {!!}

  -- hseq-eqv : ∀ {x y z} {f f' : x ~> y} {g g' : y ~> z}
  --          → (p : f ≈ f') (q : g ≈ g') (c : C.has-path f g)
  --          → Arr.hseq-transport p q c ＝ (f' ∙ g' , heqv)
  -- hseq-eqv {f'} {g'} p q (k , α) = C.comp-prop f' g' _ _

  -- identity laws are contractible
  unitr-prop : ∀ {x y} {f : x ~> y} (α β : f ∙ idn ≈ f) → f , α ≡ f , β
  unitr-prop {f} α β = comp-prop f idn (f , α) (f , β)

  eq-equiv : ∀ {x y} {f g : x ~> y} → is-equiv (eqtopath {f = f} {g})
  eq-equiv {g = g} .Equality.is-equiv.inv f = subst (_≈ g) (sym f) heqv
  eq-equiv .Equality.is-equiv.unit h = {!!}
  eq-equiv .Equality.is-equiv.counit = {!!}
  eq-equiv .Equality.is-equiv.adj = {!!}
