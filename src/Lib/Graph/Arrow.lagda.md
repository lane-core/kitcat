```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph
open import Lib.Graph.Virtual

module Lib.Graph.Arrow {u v} (G : Virtual-graph u v) where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Path
open import Lib.Underlying

open Graph (G .fst) renaming (₀ to Ob; ₁ to infix 4 _~>_)
open virtual-equipment (G .snd)
  renaming ( concat to infixr 40  _∙_
           ; vconcat to infixr 40  _⨾_
           ; hconcat to infixr 50 _●_ )

cofibroid : {x y z : Ob} → x ~> y → x ~> z → Type v
cofibroid {y = y} {z} f s = Σ h ∶ (y ~> z) , f ∙ h => s

fibroid : {w x y : Ob} → x ~> y → w ~> y → Type v
fibroid {w} {x} f s = Σ h ∶ w ~> x , h ∙ f => s

has-path : {x y z : Ob} → x ~> y → y ~> z → Type v
has-path {x} {z} f g = Σ h ∶ x ~> z , f ∙ g => h

is-left-cocartesian : {x y z : Ob} (p : x ~> y) (q : x ~> z) → Type v
is-left-cocartesian p q = is-contr (cofibroid p q)

is-right-cocartesian : {w x y : Ob} (p : x ~> y) (q : w ~> y) → Type v
is-right-cocartesian p q = is-contr (fibroid p q)

hseq-transport : {x y z : Ob} {f f' : x ~> y} {g g' : y ~> z}
               → f => f' → g => g' → has-path f g → has-path f' g'
hseq-transport p q (k , α) = (k , hsym (p ● q) ⨾ α)

record is-cocartesian {x y : Ob} (q : x ~> y) : Type (u ⊔ v) where
  field
    left : (∀ {z : Ob} (s : x ~> z) → is-left-cocartesian q s)
    right :(∀ {w : Ob} (s : w ~> y) → is-right-cocartesian q s)

_≅_ : Ob → Ob → Type (u ⊔ v)
x ≅ y = Σ f ∶ x ~> y , is-cocartesian f
infix 4 _≅_

idtohom : ∀ {x y} (i : x ~> x) (f : x ＝ y) → x ~> y
idtohom {x} i f = subst (x ~>_) f i

idtohom-op : ∀ {x y} (i : y ~> y) (f : x ＝ y) → x ~> y
idtohom-op {y} i f = subst (_~> y) (sym f) i

idtohom2 : ∀ {x y}  {f g : x ~> y} (i : f => f) (H : f ＝ g) → f => g
idtohom2 {f} i H = subst (f =>_) H i

idtohom2-op : ∀ {x y}  {f g : x ~> y} (i : g => g) (H : f ＝ g) → f => g
idtohom2-op {g} i H = subst (_=> g) (sym H) i

module cocartesian {x y : Ob} (q : x ~> y) (p : is-cocartesian q) where
  unit-equiv = is-cocartesian.right p
  counit-equiv = is-cocartesian.left p

  private module unit {w : Ob} (s : w ~> y) = is-contr (unit-equiv s)
  private module counit {z : Ob} (s : x ~> z) = is-contr (counit-equiv s)

  divl : ∀ {w} (s : w ~> y) → w ~> x
  divl s = unit.center s .fst

  lhtpy : ∀ {w} (s : w ~> y) →  divl s ∙ q => s
  lhtpy s = unit.center s .snd

  lpaths : ∀ {w} (s : w ~> y) ((e , u) : fibroid q s) → (divl s , lhtpy s) ＝ (e , u)
  lpaths = unit.paths

  unit-prop : ∀ {w} (s : w ~> y) → is-prop (fibroid q s)
  unit-prop s f g = cat (sym (lpaths s f)) (lpaths s g)

  divr : ∀ {z} → x ~> z → y ~> z
  divr s = counit.center s .fst

  rhtpy : ∀ {z} → (s : x ~> z) →  q ∙ divr s => s
  rhtpy s = counit.center s .snd

  rpaths : ∀ {z} → (s : x ~> z) ((e , u) : cofibroid q s) → (divr s , rhtpy s) ＝ (e , u)
  rpaths = counit.paths

  counit-prop : ∀ {z} (s : x ~> z) → is-prop (cofibroid q s)
  counit-prop s f g = cat (sym (rpaths s f)) (rpaths s g)

  unit : x ~> x
  unit = divl q

  counit : y ~> y
  counit = divr q

  lsym : y ~> x
  lsym = divl counit

  rsym : y ~> x
  rsym = divr unit

  invl :  lsym ∙ q => counit
  invl = lhtpy counit

  invr : q ∙ rsym => unit
  invr = rhtpy unit

  unit-path : unit ∙ q => q
  unit-path = lhtpy q

  counit-path : q ∙ counit => q
  counit-path = rhtpy q

  midpoint : unit ∙ q => q ∙ counit
  midpoint = unit-path ⨾ hsym counit-path

  hunit : q => q
  hunit = hsym unit-path ⨾ unit-path

  hcounit : q => q
  hcounit = hsym counit-path ⨾ counit-path

  loop : q => q
  loop = hunit ⨾ hcounit

record is-unital (x : Ob) : Type (u ⊔ v) where
  field
    idn : x ~> x
    iso : is-cocartesian idn
    thk : {w : Ob} (f : w ~> x) → ((f ∙ idn) ∙ idn) => (f ∙ idn)
    lin : {y : Ob} (f : x ~> y) → (idn ∙ (idn ∙ f)) => (idn ∙ f)


```
module unital {x : Ob} (unit : is-unital x) where
  private module unit = is-unital unit
  private module iso = cocartesian unit.idn unit.iso

  idn : x ~> x
  idn = unit.idn

  loop : idn => idn
  loop = iso.loop

  is-thk = unit.thk
  is-lin = unit.lin

  right-cocartesian = iso.unit-equiv
  left-cocartesian = iso.counit-equiv

  lin-coh : ∀ {y} (f : x ~> y) → (f , (hsym (unit.lin f) ⨾ unit.lin f)) ＝ (idn ∙ f , (unit.lin f))
  lin-coh f = is-contr→is-prop (iso.counit-equiv (idn ∙ f)) _ _

  unitl-comp : ∀ {y} (f : x ~> y) → idn ∙ f ＝ f
  unitl-comp f = cong fst (sym (lin-coh f))

  thk-coh : ∀ {w} (f : w ~> x) → (f , hsym (unit.thk f) ⨾ unit.thk f) ＝ (f ∙ idn , unit.thk f)
  thk-coh f = is-contr→is-prop (iso.unit-equiv (f ∙ idn)) _ _

  unitr-comp : ∀ {w} (f : w ~> x) → f ∙ idn ＝ f
  unitr-comp f = cong fst (sym (thk-coh f))

  unitl : ∀ {y} (f : x ~> y) → idn ∙ f => f
  unitl {y} f = subst (idn ∙ f =>_) (unitl-comp f) (hsym (unit.lin f) ⨾ unit.lin f)

  unitr : ∀ {w} (f : w ~> x) → f ∙ idn => f
  unitr f = subst (f ∙ idn =>_) (unitr-comp f) (hsym (unit.thk f) ⨾ unit.thk f)

  unit-path : idn => iso.unit
  unit-path = hsym iso.unit-path ⨾ unitr iso.unit

  counit-path : idn => iso.counit
  counit-path = hsym iso.counit-path ⨾ unitl iso.counit

  idem-coh : (idn , (unit-path ● loop ⨾ iso.unit-path))
           ＝ (idn , (loop ● counit-path ⨾ iso.counit-path))
  idem-coh = is-contr→is-prop (iso.counit-equiv idn) _ _

  idem : idn ∙ idn => idn
  idem = unit-path ● loop ⨾ iso.unit-path

  lin-unitl : ∀ {y} (f : x ~> y) → (idn ∙ f , unit.lin f) ＝ (f , (hsym (unit.lin f) ⨾ unit.lin f))
  lin-unitl f = is-contr→is-prop (iso.counit-equiv (idn ∙ f)) _ _

  thk-unitl : ∀ {w} (f : w ~> x) → (f ∙ idn , unit.thk f) ＝ (f , (hsym (unit.thk f) ⨾ unit.thk f))
  thk-unitl f = is-contr→is-prop (iso.unit-equiv (f ∙ idn)) _ _

  idn-counit : fibroid idn iso.counit
  idn-counit = idn , (unitl idn) ⨾ counit-path -- counit-path

  lsym-idn : iso.lsym ＝ idn
  lsym-idn = cong fst (iso.lpaths iso.counit idn-counit)

  idn-unit : cofibroid idn iso.unit
  idn-unit = idn , (unitr idn) ⨾ unit-path

  rsym-idn : iso.rsym ＝ idn
  rsym-idn = cong fst (iso.rpaths iso.unit idn-unit)

  lsym-rsym : iso.lsym ＝ iso.rsym
  lsym-rsym = cat (lsym-idn) (sym rsym-idn)

  lsym-path : idn => iso.lsym
  lsym-path = counit-path ⨾ hsym iso.invl ⨾ unitr iso.lsym

  rsym-path : idn => iso.rsym
  rsym-path = unit-path ⨾ hsym iso.invr ⨾ unitl iso.rsym

  sym-path : iso.lsym => iso.rsym
  sym-path = hsym lsym-path ⨾ rsym-path

  sym-path-comp : iso.lsym ＝ iso.rsym
  sym-path-comp = cat (lsym-idn) (sym (rsym-idn))

record is-composable : Type (u ⊔ v) where
  field
    comp-prop : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-prop (has-path f g)

  -- when an associator exists it is unique, and its homotopical center is the 2-cell identity map
  assoc-paths : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z)
              → ((s , p) : Σ s ∶ w ~> z , (f ∙ g) ∙ h => s)
              → ((f ∙ g) ∙ h , heqv) ＝ (s , p)
  assoc-paths f g h as = comp-prop (f ∙ g) h (((f ∙ g) ∙ h) , heqv) as

  assoc-contr : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z)
              → is-contr (has-path (f ∙ g) h)
  assoc-contr f g h .center = (f ∙ g) ∙ h , heqv
  assoc-contr f g h .paths = assoc-paths f g h

  comp-contr : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-contr (has-path f g)
  comp-contr f g .center = (f ∙ g) , heqv
  comp-contr f g .paths = comp-prop f g (f ∙ g , heqv)

  hseq-eqv : ∀ {x y z} {f f' : x ~> y} {g g' : y ~> z}
           → (p : f => f') (q : g => g')
           → (c : has-path f g) → hseq-transport p q c ＝ (f' ∙ g' , heqv)
  hseq-eqv {f'} {g'} p q (k , α) = comp-prop f' g' _ _

module composable (C : is-composable) where
  open is-composable C

  composite : ∀ {x y z} → x ~> y → y ~> z → Type v
  composite {x} {y} {z} f g = Σ s ∶ x ~> z , (f ∙ g => s)
