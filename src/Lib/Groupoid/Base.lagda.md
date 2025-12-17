```agda

{-# OPTIONS --safe --two-level --cubical-compatible #-}

module Lib.Groupoid.Base where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Equal hiding (_≃_; _≅_)

record Graph u v : Type (u ₊ ⊔ v ₊) where
  constructor gph
  field
    ₀ : Type u
    ₁ : ₀ → ₀ → Type v
{-# INLINE gph #-}

record Reflexive-graph u v : Type (u ₊ ⊔ v ₊) where
  field
    ₀ : Type u
    ₁ : ₀ → ₀ → Type u
    eqv : (x : ₀) → ₁ x x

record Homotopical-graph u v : Type₊ (u ⊔ v) where
  field
    ₀ : Type u
    graph : (x y : ₀) → Reflexive-graph v v

  private module G x y = Reflexive-graph (graph x y)
  _~>_ : ₀ → ₀ → Type v
  _~>_ = G.₀

  _≃_ : ∀ {x y} → x ~> y → x ~> y → Type v
  _≃_ {x} {y} = G.₁ x y

  heqv : ∀ {x y} {h : x ~> y} → h ≃ h
  heqv {x} {y} {h = h} = G.eqv x y h

  gph1 : Graph u v
  gph1 .Graph.₀ = ₀
  gph1 .Graph.₁ = _~>_

  gph2 : (x y : ₀) → Graph v v
  gph2 x y .Graph.₀ = x ~> y
  gph2 x y .Graph.₁ = _≃_

module _ ⦃ _ : Equality ⦄ where
  record Virtual-graph u v : Type₊ (u ⊔ v) where
    infixr 40 _∙_ _●_
    field
      graph : Homotopical-graph u v

    open Homotopical-graph graph public
    field
      _∙_ : ∀ {x y z} → x ~> y → y ~> z → x ~> z
      _●_ : ∀ {x y} {f g h : x ~> y} → f ≃ g → g ≃ h → f ≃ h
      hsym : ∀ {x y} {f g : x ~> y} → f ≃ g → g ≃ f
      hcmp : ∀ {x y z} {e1 d1 : x ~> y} {e2 d2 : y ~> z}
           → e1 ≃ d1 → e2 ≃ d2 → (e1 ∙ e2) ≃ (d1 ∙ d2)

    cofibroid : ∀ {x y z} → x ~> y → x ~> z → Type v
    cofibroid {y = y} {z} f s = Σ (λ (h : y ~> z) →  f ∙ h ≃ s)

    fibroid : ∀ {w x y} → x ~> y → w ~> y → Type v
    fibroid {w} {x} f s = Σ (λ (h : w ~> x) → h ∙ f ≃ s)

    has-path : ∀ {x y z} → x ~> y → y ~> z → Type v
    has-path {x} {z} f g = Σ (λ (h : x ~> z) → f ∙ g ≃ h)

    is-left-cocartesian : ∀ {x y z} (p : x ~> y) (q : x ~> z) → Type v
    is-left-cocartesian p q = is-contr (cofibroid p q)

    is-right-cocartesian : ∀ {w x y} (p : x ~> y) (q : w ~> y) → Type v
    is-right-cocartesian p q = is-contr (fibroid p q)

    is-cocartesian : ∀ {x y} → x ~> y → Type (u ⊔ v)
    is-cocartesian {x} {y} q = (∀ {z} (s : x ~> z) → is-left-cocartesian q s)
                             × (∀ {w} (s : w ~> y) → is-right-cocartesian q s)

    hcmp2 : ∀ {x y} {f g h : x ~> y} {e1 d1 : f ≃ g} {e2 d2 : g ≃ h}
           → e1 ＝ d1 → e2 ＝ d2 → (e1 ● e2) ＝ (d1 ● d2)
    hcmp2 {e1} {e2} H K = subst2 (λ s r → e1 ● e2 ＝ s ● r) H K refl

    hcmp-transport : ∀ {x y z} {f f' : x ~> y} {g g' : y ~> z}
                   → f ≃ f' → g ≃ g' → has-path f g → has-path f' g'
    hcmp-transport p q (k , α) = (k , hsym (hcmp p q) ● α)

    h-vgph : ∀ x y → Virtual-graph v v
    h-vgph x y .graph .Homotopical-graph.₀ = x ~> y
    h-vgph x y .graph .Homotopical-graph.graph f g .Reflexive-graph.₀ = f ≃ g
    h-vgph x y .graph .Homotopical-graph.graph f g .Reflexive-graph.₁ = _＝_
    h-vgph x y .graph .Homotopical-graph.graph f g .Reflexive-graph.eqv = λ x → refl
    h-vgph x y ._∙_ = _●_
    h-vgph x y ._●_ = cat
    h-vgph x y .hsym = sym
    h-vgph x y .hcmp = hcmp2

    _≅_ : ₀ → ₀ → Type (u ⊔ v)
    x ≅ y = Σ (λ (f : x ~> y) → is-cocartesian f)

  record Semicategory u v : Type₊ (u ⊔ v) where
    field
      vgraph : Virtual-graph u v

    open Virtual-graph vgraph renaming (₀ to Ob) public
    field
      composites-prop : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-prop (has-path f g)

    assoc-prop : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z) → (as : (f ∙ g) ∙ h ≃ f ∙ g ∙ h)
          → ((f ∙ g) ∙ h , heqv) ＝ (f ∙ g ∙ h , as)
    assoc-prop f g h as = composites-prop (f ∙ g) h (((f ∙ g) ∙ h) , heqv) ((f ∙ g ∙ h) , as)

    composites-contr : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-contr (has-path f g)
    composites-contr f g .center = (f ∙ g) , heqv
    composites-contr f g .paths = composites-prop f g (f ∙ g , heqv)

    hcmp-eqv : ∀ {x y z} {f f' : x ~> y} {g g' : y ~> z}
             → (p : f ≃ f') (q : g ≃ g')
             → (c : has-path f g) → hcmp-transport p q c ＝ (f' ∙ g' , heqv)
    hcmp-eqv {f'} {g'} p q (k , α) = composites-prop f' g' _ _



  record semicategory-like u v : Type₊ (u ⊔ v) where
    field
      vgraph : Virtual-graph u v

    open Virtual-graph vgraph renaming (₀ to Ob) public
    field
      composites-prop : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-prop (has-path f g)

    assoc-prop : ∀ {w x y z} (f : w ~> x) (g : x ~> y) (h : y ~> z) → (as : (f ∙ g) ∙ h ≃ f ∙ g ∙ h)
          → ((f ∙ g) ∙ h , heqv) ＝ (f ∙ g ∙ h , as)
    assoc-prop f g h as = composites-prop (f ∙ g) h (((f ∙ g) ∙ h) , heqv) ((f ∙ g ∙ h) , as)

    composites-contr : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-contr (has-path f g)
    composites-contr f g .center = (f ∙ g) , heqv
    composites-contr f g .paths = composites-prop f g (f ∙ g , heqv)

    hcmp-eqv : ∀ {x y z} {f f' : x ~> y} {g g' : y ~> z}
             → (p : f ≃ f') (q : g ≃ g')
             → (c : has-path f g) → hcmp-transport p q c ＝ (f' ∙ g' , heqv)
    hcmp-eqv {f'} {g'} p q (k , α) = composites-prop f' g' _ _


```

module _ {u v} (G : Graph u v) where
  private module G = Graph G

  data Directed-path : G.₀ → G.₀ → Type (u ⊔ v) where
    rfl : ∀ {x} → Directed-path x x
    comp : ∀ {x y z} → G.₁ x y → Directed-path y z → Directed-path x z

record Magmoid u v : Type (u ₊ ⊔ v ₊) where
  field
    Ob : Type u
    _~>_ : Ob → Ob → Type u
    _∙_ : ∀ {x y z} → x ~> y → y ~> z → x ~> z


record Bimagmoid u v : Type₊ (u ⊔ v) where
  infix 4 _↝_ _⇒_
  infixr 7 _∙_ _●_
  field
    Ob : Type u
    _↝_ : Ob → Ob → Type v
    _⇒_ : ∀ {x y} → x ↝ y → x ↝ y → Type v
    _∙_ : ∀ {x y z} → x ↝ y → y ↝ z → x ↝ z
    _●_ : ∀ {x y} {f g h : x ↝ y} → f ⇒ g → g ⇒ h → f ⇒ h
    hcmp : ∀ {x y z} {e1 d1 : x ↝ y} {e2 d2 : y ↝ z}
         → e1 ⇒ d1 → e2 ⇒ d2 → (e1 ∙ e2) ⇒ (d1 ∙ d2)

  composite : ∀ {x y z} → x ↝ y → y ↝ z → Type v
  composite {x} {z} f g = Σ (λ (h : x ↝ z) → f ∙ g ⇒ h)

  cofibroid : ∀ {x y z} → x ↝ y → x ↝ z → Type v
  cofibroid {y = y} {z} f s = Σ (λ (h : y ↝ z) →  (f ∙ h) ⇒ s)

  fibroid : ∀ {w x y} → x ↝ y → w ↝ y → Type v
  fibroid {w} {x} f s = Σ (λ (h : w ↝ x) → (h ∙ f) ⇒ s)

module _ ⦃ E : Equality ⦄ where
  module _ {u v} (C : Bimagmoid u v)
    (let open Bimagmoid C renaming (_⇒_ to _≃_))
    (hsym : ∀ {x y} {e d : x ↝ y} → e ≃ d → d ≃ e)
    where
    record is-isomorphism {x y} (q : x ↝ y) : Type (u ⊔ v) where
      field
        unit-equiv : ∀ {w} (s : w ↝ y) → is-contr (fibroid q s)
        counit-equiv : ∀ {z} (s : x ↝ z) → is-contr (cofibroid q s)

      private module unit {w} (s : w ↝ y) = is-contr (unit-equiv s)
      private module counit {z} (s : x ↝ z) = is-contr (counit-equiv s)

      divl : ∀ {w} (s : w ↝ y) → w ↝ x
      divl s = unit.center s .fst

      lhtpy : ∀ {w} (s : w ↝ y) →  divl s ∙ q ≃ s
      lhtpy s = unit.center s .snd

      lpaths : ∀ {w} (s : w ↝ y) ((e , u) : fibroid q s) → (divl s , lhtpy s) ＝ (e , u)
      lpaths = unit.paths

      divr : ∀ {z} → x ↝ z → y ↝ z
      divr s = counit.center s .fst

      rhtpy : ∀ {z} → (s : x ↝ z) →  q ∙ divr s ≃ s
      rhtpy s = counit.center s .snd

      rpaths : ∀ {z} → (s : x ↝ z) ((e , u) : cofibroid q s) → (divr s , rhtpy s) ＝ (e , u)
      rpaths = counit.paths

      unit : x ↝ x
      unit = divl q

      counit : y ↝ y
      counit = divr q

      lsym : y ↝ x
      lsym = divl counit

      rsym : y ↝ x
      rsym = divr unit

      invl :  lsym ∙ q ≃ counit
      invl = lhtpy counit

      invr : q ∙ rsym ≃ unit
      invr = rhtpy unit

      unit-path : unit ∙ q ≃ q
      unit-path = lhtpy q

      counit-path : q ∙ counit ≃ q
      counit-path = rhtpy q

      midpoint : unit ∙ q ≃ q ∙ counit
      midpoint = unit-path ● hsym counit-path

      hunit : q ≃ q
      hunit = hsym unit-path ● unit-path

      hcounit : q ≃ q
      hcounit = hsym counit-path ● counit-path

      loop : q ≃ q
      loop = hunit ● hcounit

      -- sym-assoc : q ∙ lsym ∙ q ≃ (q ∙ rsym) ∙ q
      -- sym-assoc = (counit-path ● hcmp hunit invl) ● hsym (unit-path ● hcmp invr hcounit)

    record is-unital (x : Ob) : Type (u ⊔ v) where
      field
        idn : x ↝ x
        iso : is-isomorphism idn
        thk : ∀ {w} (f : w ↝ x) → ((f ∙ idn) ∙ idn) ≃ (f ∙ idn) -- idn is thunkable
        lin : ∀ {y} (f : x ↝ y) → (idn ∙ (idn ∙ f)) ≃ (idn ∙ f) -- idn is linear

      private module iso = is-isomorphism iso

      loop = iso.loop

      lin-coh : ∀ {y} (f : x ↝ y) → (f , (hsym (lin f) ● lin f)) ＝ (idn ∙ f , (lin f))
      lin-coh f = is-contr→is-prop (iso.counit-equiv (idn ∙ f)) _ _

      unitl-comp : ∀ {y} (f : x ↝ y) → idn ∙ f ＝ f
      unitl-comp f = cong fst (sym (lin-coh f))

      thk-coh : ∀ {w} (f : w ↝ x) → (f , hsym (thk f) ● thk f) ＝ (f ∙ idn , thk f)
      thk-coh f = is-contr→is-prop (iso.unit-equiv (f ∙ idn)) _ _

      unitr-comp : ∀ {w} (f : w ↝ x) → f ∙ idn ＝ f
      unitr-comp f = cong fst (sym (thk-coh f))

      unitl : ∀ {y} (f : x ↝ y) → idn ∙ f ≃ f
      unitl {y} f = subst (idn ∙ f ≃_) (unitl-comp f) (hsym (lin f) ● lin f)

      unitr : ∀ {w} (f : w ↝ x) → f ∙ idn ≃ f
      unitr f = subst (f ∙ idn ≃_) (unitr-comp f) (hsym (thk f) ● thk f)

      unit-path : idn ≃ iso.unit
      unit-path = hsym iso.unit-path ● unitr iso.unit -- iso.unit-path ● unitr iso.unit

      counit-path : idn ≃ iso.counit
      counit-path = hsym iso.counit-path ● unitl iso.counit -- iso.counit-path ● unitl iso.counit

      idem-coh : (idn , (hcmp unit-path loop ● iso.unit-path))
               ＝ (idn , (hcmp loop counit-path ● iso.counit-path))
      idem-coh = is-contr→is-prop (iso.counit-equiv idn) (idn , _) (idn , _)

      idem : idn ∙ idn ≃ idn
      idem = hcmp unit-path loop ● iso.unit-path

      lin-unitl : ∀ {y} (f : x ↝ y) → (idn ∙ f , lin f) ＝ (f , (hsym (lin f) ● lin f))
      lin-unitl f = is-contr→is-prop (iso.counit-equiv (idn ∙ f)) _ _

      thk-unitl : ∀ {w} (f : w ↝ x) → (f ∙ idn , thk f) ＝ (f , (hsym (thk f) ● thk f))
      thk-unitl f = is-contr→is-prop (iso.unit-equiv (f ∙ idn)) _ _

      idn-counit : fibroid idn iso.counit
      idn-counit = idn , (unitl idn) ● counit-path -- counit-path

      lsym-idn : iso.lsym ＝ idn
      lsym-idn = cong fst (iso.lpaths iso.counit idn-counit)

      idn-unit : cofibroid idn iso.unit
      idn-unit = idn , (unitr idn) ● unit-path

      rsym-idn : iso.rsym ＝ idn
      rsym-idn = cong fst (iso.rpaths iso.unit idn-unit)

      lsym-rsym : iso.lsym ＝ iso.rsym
      lsym-rsym = cat (lsym-idn) (sym rsym-idn)

      lsym-path : idn ≃ iso.lsym
      lsym-path = counit-path ● hsym iso.invl ● unitr iso.lsym

      rsym-path : idn ≃ iso.rsym
      rsym-path = unit-path ● hsym iso.invr ● unitl iso.rsym

      sym-path : iso.lsym ≃ iso.rsym
      sym-path = hsym lsym-path ● rsym-path

  module _ {u v} (C : Bimagmoid u v)
    (let open Bimagmoid C renaming (_⇒_ to _≃_))
    where

    hom-str : Ob → Ob → Bimagmoid v v
    hom-str x y .Bimagmoid.Ob = x ↝ y
    hom-str x y .Bimagmoid._↝_ = _≃_
    hom-str x y .Bimagmoid._⇒_ = _＝_
    hom-str x y .Bimagmoid._∙_ = _●_
    hom-str x y .Bimagmoid._●_ = cat
    hom-str x y .Bimagmoid.hcmp {e1} {d1} {e2} {d2} p q =
      subst2 (λ r s → e1 ● e2 ＝ r ● s) p q refl

  record Pretypoid u v : Type₊ (u ⊔ v) where
    field
      str : Bimagmoid u v

    open Bimagmoid str public renaming (_⇒_ to _≃_)

    field
      hsym : ∀ {x y} {e d : x ↝ y} → e ≃ d → d ≃ e

      hsym-invl : ∀ {x y} {e d : x ↝ y} (h : e ≃ d) → hsym h ● h ＝ {!!}
      hsym-invr : ∀ {x y} {e d : x ↝ y} (h : e ≃ d) → h ● hsym h ＝ {!!}
      unital : ∀ x → is-unital str hsym x
    private module idn {x} = is-unital (unital x)

    field
      h-unital : ∀ {x y} (e : x ↝ y) → is-unital (hom-str str x y) sym e
      h-assoc : ∀ {x y} {e f g h : x ↝ y} (q : e ≃ f) (r : f ≃ g) (s : g ≃ h)
              → q ● r ● s ＝ (q ● r) ● s

    open idn using (idn; idem; unitl; unitr; unitl-comp; unitr-comp)
    -- field
    --   invr : ∀ {x y} {e d : x ↝ y} (h : e ≃ d) → h ● hsym h ＝ {!!}




  -- is-linear : ∀ ⦃ E : Equality ⦄ {x y} → x ↝ y → Type (u ⊔ v)
  -- is-linear q = ∀ {w} (s : w ↝ _) → is-prop (fibroid q s)

  --   -- q is thunkable: postcomposition (q ∙ _) is an embedding
  -- is-thunkable : ∀ ⦃ E : Equality ⦄ {x y} → x ↝ y → Type (u ⊔ v)
  -- is-thunkable q = ∀ {z} (s : _ ↝ z) → is-prop (cofibroid q s)


```

  -- record is-unital {u v} {Ob : Type u}
  --   (_≡_ : Ob → Ob → Type v)
  --   (_∙_ : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z)
  --   (x : Ob) : Type (u ⊔ v)
  --   where
  --     field
  --       idn : x ≡ x
  --       iso : is-iso-on _≡_ _∙_ idn
  --       thk : ∀ {w} (f : w ≡ x) → (f ∙ idn) ∙ idn ＝ f ∙ idn
  --       lin : ∀ {y} (f : x ≡ y) → idn ∙ (idn ∙ f) ＝ idn ∙ f
  --     open is-iso-on iso

--   record Typoid-on {u} {Ob : Type u}
--     (_≡_ : Ob → Ob → Type u)
--     (_∙_ : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z)
--     {x y : Ob} (q : x ≡ y)
--     : Type (u ₊)
--     where
--     infix 2 _≃_
--     field
--       _≃_ : ∀ {w z} → w ≡ z → w ≡ z → Type u
--       sym : y ≡ x
--       unit : x ≡ x
--       counit : y ≡ y
--       unitl : unit ∙ q ≃ q
--       unitr : q ∙ counit ≃ q
--       invl : sym ∙ q ≃ counit
--       invr : q ∙ sym ≃ unit

--       -- horiz : {x y z : Ob} {e1 d1 : x ≡ y} {e2 d2 : y ≡ z}
--       --       → e1 ≃ d1 → e2 ≃ d2 → ? ≡ d1 ∙ d2

--   --record has-identity {u} {Ob : Type Ob}
--   record Typoid {u} (Ob : Type u) : Type u where
--     field
--       unitl : {x y : Ob} (p : x ＝ y) → refl ∙ p  ＝ p
--       unitr : {x y : Ob} (p : x ＝ y) → p ∙ refl  ＝ p
--       invl : {x y : Ob} (p : x ＝ y) → sym p ∙ p ＝ refl
--       invr : {x y : Ob} (p : x ＝ y) → p ∙ sym p ＝ refl
--       assoc : {w x y z : Ob} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
--             → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
--       horiz : {x y z : Ob} {e1 d1 : x ＝ y} {e2 d2 : y ＝ z}
--             → e1 ＝ d1 → e2 ＝ d2 → e1 ∙ e2 ＝ d1 ∙ d2

-- -- module _ ⦃ E : Equality ⦄ where
-- --   record Typoid {u} (Ob : Type u) : Type u where
-- --     field
-- --       unitl : {x y : Ob} (p : x ＝ y) → refl ∙ p  ＝ p
-- --       unitr : {x y : Ob} (p : x ＝ y) → p ∙ refl  ＝ p
-- --       invl : {x y : Ob} (p : x ＝ y) → sym p ∙ p ＝ refl
-- --       invr : {x y : Ob} (p : x ＝ y) → p ∙ sym p ＝ refl
-- --       assoc : {w x y z : Ob} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
-- --             → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
-- --       horiz : {x y z : Ob} {e1 d1 : x ＝ y} {e2 d2 : y ＝ z}
-- --             → e1 ＝ d1 → e2 ＝ d2 → e1 ∙ e2 ＝ d1 ∙ d2

--     record is-unital' (x : Ob) : Type (u ⊔ v) where
--       field
--         idn : x ↝ x

--         -- Section side (contractible) — FIXED
--         divl : ∀ {w} (s : w ↝ x) → w ↝ x
--         unit : ∀ {w} (s : w ↝ x) → s ≃ divl s ∙ idn
--         unit-equiv  : ∀ {w} (s : w ↝ x) → is-contr (fibroid idn s)

--         -- Raw retraction
--         divr0 : ∀ {z} (s : x ↝ z) → x ↝ z
--         counit0 : ∀ {z} (s : x ↝ z) → s ≃ idn ∙ divr0 s
--         thk-path : ∀ {w} (f : w ↝ x) → f ∙ idn ≃ divl (f ∙ idn)

--       round : (s : x ↝ x) → x ↝ x
--       round s = divl (idn ∙ divr0 s) ∙ idn

--       divr : (s : x ↝ x) → x ↝ x
--       divr s = divr0 (round s)

--       counit : (s : x ↝ x) → s ≃ idn ∙ divr s
--       counit s = counit0 s ● unit (idn ∙ divr0 s) ● counit0 (round s)

--       η : x ↝ x
--       η = divl idn

--       ε0 : x ↝ x
--       ε0 = divr0 idn

--       ε : x ↝ x
--       ε = divr0 (round idn)

--       round-idn : x ↝ x
--       round-idn = divl (idn ∙ ε0) ∙ idn

--       unit-idn : idn ≃ η ∙ idn
--       unit-idn = unit idn

--       counit0-idn : idn ≃ idn ∙ ε0
--       counit0-idn = counit0 idn

--       counit-idn : idn ≃ idn ∙ ε
--       counit-idn = counit idn

--       loop : ∀ {w} (f : w ↝ x) → f ≃ f
--       loop f = unit f ● hsym (unit f)

--       coloop : ∀ {z} (f : x ↝ z) → f ≃ f
--       coloop f = counit0 f ● hsym (counit0 f)

--       divl-absorbs : ∀ {w} (f : w ↝ x) → divl (f ∙ idn) ＝ f
--       divl-absorbs f = cong fst (is-contr→is-prop (unit-equiv (f ∙ idn))
--                                                   (divl (f ∙ idn) , unit (f ∙ idn))
--                                                   (f , hcmp (loop f) (loop idn)))

--       thk : ∀ {w} (f : w ↝ x) → ((f ∙ idn) ∙ idn) ≃ (f ∙ idn)
--       thk f = hcmp (thk-path f) (loop idn) ● hcmp (subst (divl (f ∙ idn) ≃_) (divl-absorbs f) (loop (divl (f ∙ idn)))) (loop idn)

--     record is-isomorphism' {x y : Ob} (q : x ↝ y) : Type (u ⊔ v) where
--       field
--         divl : ∀ {w} → w ↝ y → w ↝ x
--         divr : ∀ {z} → x ↝ z → y ↝ z
--         unit : ∀ {w} (s : w ↝ y) → s ≃ divl s ∙ q
--         counit : ∀ {z} (s : x ↝ z) → s ≃ q ∙ divr s

--       idl : ∀ {w} → w ↝ y → w ↝ y
--       idl s = divl s ∙ q

--       idr : ∀ {z} → x ↝ z → x ↝ z
--       idr s = q ∙ divr s

--       field
--         adj : ∀ {w} (f : x ↝ y) → ({!!} ● hcmp {!!} (unit f) ● {!!}) ＝ counit f

--       -- round : (s : x ↝ y) → x ↝ y
--       -- round s = divl (q ∙ divr0 s) ∙ q

--       -- divr : ∀ {z} (s : x ↝ z) → {!!} ↝ {!!}
--       -- divr s = divr0 (round {!!})

--       -- counit : ∀ {z} (s : x ↝ z) → s ≃ q ∙ divr s
--       -- counit s = counit0 s ● unit (q ∙ divr s) ● counit (round s)

--   record is-unital-on {u v} {Ob : Type u}
--     (_≡_ : Ob → Ob → Type v)
--     (_∙_ : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z)
--     {x y : Ob} (q : x ≡ y) : Type (u ⊔ v)
--     where
--     field
--       lcomp : ∀ {w} (s : w ≡ y) → is-contr (fiber (_∙ q) s)
--       rcomp : ∀ {z} (s : x ≡ z) → is-contr (fiber (q ∙_) s)

--     module unit {w} (s : w ≡ y) = Σ (is-contr.center (lcomp s))
--     module counit {z} (s : x ≡ z) = Σ (is-contr.center (rcomp s))

--     divl : ∀ {w} (s : w ≡ y) → w ≡ x
--     divl = unit.fst

--     idl : ∀ {w} → w ≡ y → w ≡ y
--     idl s = divl s ∙ q

--     divl-coh : ∀ {w} (s : w ≡ y) → idl s ＝ s
--     divl-coh = unit.snd

--     divr : ∀ {z} (s : x ≡ z) → y ≡ z
--     divr = counit.fst

--     idr : ∀ {z} → x ≡ z → x ≡ z
--     idr s = q ∙ divr s

--     divr-coh : ∀ {z} (s : x ≡ z) → idr s ＝ s
--     divr-coh = counit.snd

--     unit : x ≡ x
--     unit = divl q

--     counit : y ≡ y
--     counit = divr q

--     lsym : y ≡ x
--     lsym = divl counit

--     rsym : y ≡ x
--     rsym = divr unit

--     invl : lsym ∙ q ＝ counit
--     invl = divl-coh counit

--     invr : q ∙ rsym ＝ unit
--     invr = divr-coh unit
