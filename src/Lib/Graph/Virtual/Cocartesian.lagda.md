```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Lib.Graph.Base
open import Lib.Graph.Virtual.Base
module Lib.Graph.Virtual.Cocartesian {u v w} (V : V-graph u v w) where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.HLevel
open import Lib.Core.Base
open import Lib.Core.Kan using (hcomp; hfill; transport-filler)


open V-graph V
  renaming ( ₀ to Ob
           ; ₁ to infix 4 _~>_
           ; ₂ to infix 4 _=>_
           ; concat to infixr 40 _∙_
           ; vconcat to infixr 40 _⊚_ )


  -- ctr : ∀ {a} (q : fam a) → is-contr (Σ q ∶ fam a , P a q)
  -- ctr .Equality.center = {! !} , {!!}
  -- ctr .Equality.paths = {!!}

record is-eq-rel {u} {A : Type u} (R : A → A → Type u) : Type u where
  field
    prop : ∀ {x y} → is-prop (R x y)
    eqv : {x : A} → R x x
    inv : ∀ {x y} → R x y → R y x
    cat : ∀ {x y z} → R x y → R y z → R x z

-- module EqRel u where
--   ob : Type₊ u
--   ob = Σ A ∶ Type u , Σ R ∶ (A → A → Type u) , is-set A × is-eq-rel R

--   module ob (x : ob) where
--     ₀ = x .fst
--     rel = x .snd .fst
--     ctx-set = x .snd .snd .fst
--     eq-rel = x .snd .snd .snd

--   record hom (A B : ob) : Type u where
--     private
--       module A = ob A
--       module B = ob B
--     field
--       F₀ : B.₀ → A.₀
--       coh : ∀ {x y} → B.rel x y → A.rel (F₀ x) (F₀ y)


```

Cocartesian morphisms and isomorphism

```

module _ {A B} {h : A ~> B} {ψ f : A ~> B} (α : ψ => f) where
  --is-cocartesian : {ψ : }
  -- is-left-cocartesian : Type (u ⊔ v ⊔ w)
  -- is-left-cocartesian = ∀ {w z} {Ξ : y ~> z} {s : x ~> z} (β : ψ ∙ Ξ => s)
  --                     → is-contr (Σ β/α ∶ ({!crefl!} ∙ ψ ≡ {!!}) , {!!})

is-left-embedding : {x y : Ob} → x ~> y → Type (u ⊔ v ⊔ w)
is-left-embedding {x} f = ∀ {z : Ob} (s : x ~> z) → is-prop (cofibroid f s)

is-right-embedding : {x y : Ob} → x ~> y → Type (u ⊔ v ⊔ w)
is-right-embedding {y} f = ∀ {w : Ob} (s : w ~> y) → is-prop (fibroid f s)

is-left-divisible : {x y : Ob} → x ~> y → Type (u ⊔ v ⊔ w)
is-left-divisible {x} f = ∀ {z : Ob} (s : x ~> z) → is-contr (cofibroid f s)

is-right-divisible : {x y : Ob} → x ~> y → Type (u ⊔ v ⊔ w)
is-right-divisible {y} f = ∀ {w : Ob} (s : w ~> y) → is-contr (fibroid f s)

record is-isomorphism {x y : Ob} (q : x ~> y) : Type (u ⊔ v ⊔ w) where
  field
    left : is-left-divisible q
    right : is-right-divisible q

_≅_ : Ob → Ob → Type (u ⊔ v ⊔ w)
x ≅ y = Σ f ∶ x ~> y , is-isomorphism f
infix 4 _≅_

is-isomorphism-is-prop : {x y : Ob} (q : x ~> y) → is-prop (is-isomorphism q)
is-isomorphism-is-prop q x y i .is-isomorphism.left s = is-contr-is-prop (cofibroid q s) (x .is-isomorphism.left s) (y .is-isomorphism.left s) i
is-isomorphism-is-prop q x y i .is-isomorphism.right s = is-contr-is-prop (fibroid q s) (x .is-isomorphism.right s) (y .is-isomorphism.right s) i

module cocartesian {x y : Ob} (q : x ~> y) (p : is-isomorphism q) where
  unit-equiv = is-isomorphism.right p
  counit-equiv = is-isomorphism.left p

  private module unit {w : Ob} (s : w ~> y) = is-contr (unit-equiv s)
  private module counit {z : Ob} (s : x ~> z) = is-contr (counit-equiv s)

  divl : ∀ {w} (s : w ~> y) → w ~> x
  divl s = unit.center s .fst

  lhtpy : ∀ {w} (s : w ~> y) →  divl s ∙ q => s
  lhtpy s = unit.center s .snd

  lpaths : ∀ {w} (s : w ~> y) ((e , u) : fibroid q s) → (divl s , lhtpy s) ≡ (e , u)
  lpaths = unit.paths

  unit-prop : ∀ {w} (s : w ~> y) → is-prop (fibroid q s)
  unit-prop s = is-contr→is-prop (unit-equiv s)

  divr : ∀ {z} → x ~> z → y ~> z
  divr s = counit.center s .fst

  rhtpy : ∀ {z} → (s : x ~> z) →  q ∙ divr s => s
  rhtpy s = counit.center s .snd

  rpaths : ∀ {z} → (s : x ~> z) ((e , u) : cofibroid q s) → (divr s , rhtpy s) ≡ (e , u)
  rpaths = counit.paths

  counit-prop : ∀ {z} (s : x ~> z) → is-prop (cofibroid q s)
  counit-prop s = is-contr→is-prop (counit-equiv s)

  unit : x ~> x
  unit = divl q

  unit-unique : is-prop (cofibroid q unit)
  unit-unique = counit-prop unit

  unitp : unit ∙ q => q
  unitp = lhtpy q

  -- fibroid q s = Σ h : w ~> x, h ∙ q => s
  -- For s = q: fibroid q q = Σ h : x ~> x, h ∙ q => q
  -- Center: (unit, unitp)
  J-unit : ∀ {ℓ} → (P : (h : x ~> x) → h ∙ q => q → Type ℓ)
         → P unit (lhtpy q)
         → ∀ h α → P h α
  J-unit P base h α = subst (λ (h , α) → P h α) (lpaths q (h , α)) base

  counit : y ~> y
  counit = divr q

  counit-unique : is-prop (fibroid q counit)
  counit-unique = unit-prop counit

  counitp : q ∙ counit => q
  counitp = rhtpy q

  -- cofibroid q s = Σ h : y ~> z, q ∙ h => s
  -- For s = q: cofibroid q q = Σ h : y ~> y, q ∙ h => q
  -- Center: (counit, counitp)
  J-counit : ∀ {ℓ} (P : (h : y ~> y) → q ∙ h => q → Type ℓ)
           → P counit (rhtpy q)
           → ∀ h α → P h α
  J-counit P base h α = subst (λ (h , α) → P h α) (rpaths q (h , α)) base

  lsym : y ~> x
  lsym = divl counit

  lsym-unique : (h : y ~> x) → q ∙ h => q ∙ lsym → lsym ≡ h
  lsym-unique h α = ap fst (counit-prop (q ∙ lsym) (lsym , crefl) (h , α))

  lsym-contr : is-contr (Σ r ∶ y ~> x , q ∙ r  => (q ∙ lsym))
  lsym-contr .center = lsym , crefl
  lsym-contr .paths (r , ε) i = (lsym-unique r ε i) , counit-prop (q ∙ lsym) (lsym , crefl) (r , ε) i .snd

  rsym-contr : is-contr (Σ s ∶ y ~> x , s ∙ q  => divr (divl q) ∙ q)
  rsym-contr .center = divr (divl q) , crefl
  rsym-contr .paths (r , ε) i = unit-prop (divr unit ∙ q) (divr unit , crefl) (r , ε) i

  rsym : y ~> x
  rsym = rsym-contr .center .fst

  J-lsym : ∀ {ℓ} (P : (r : y ~> x) → q ∙ r => q ∙ lsym → Type ℓ)
         → P lsym crefl
         → ∀ r ε → P r ε
  J-lsym P base r ε = subst (λ (r , ε) → P r ε) (lsym-contr .paths (r , ε)) base

  J-rsym : ∀ {ℓ} (P : (s : y ~> x) → s ∙ q => rsym ∙ q → Type ℓ)
         → P rsym crefl
         → ∀ s ε → P s ε
  J-rsym P base s ε = subst (λ (s , ε) → P s ε) (rsym-contr .paths (s , ε)) base

  -- to-path for unit
  unit-to-path : (h : x ~> x) → h ∙ q => q → unit ≡ h
  unit-to-path h α = ap fst (lpaths q (h , α))

  -- to-path for counit
  counit-to-path : (h : y ~> y) → q ∙ h => q → counit ≡ h
  counit-to-path h α = ap fst (rpaths q (h , α))

  -- to-path for lsym
  lsym-to-path : (r : y ~> x) → q ∙ r => q ∙ lsym → lsym ≡ r
  lsym-to-path r ε = ap fst (lsym-contr .paths (r , ε))

  -- to-path for rsym
  rsym-to-path : (s : y ~> x) → s ∙ q => rsym ∙ q → rsym ≡ s
  rsym-to-path s ε = ap fst (rsym-contr .paths (s , ε))

  invl-contr : is-contr (Σ h ∶ y ~> x , h ∙ q => counit)
  invl-contr = unit-equiv counit

  invl : lsym ∙ q => counit
  invl = invl-contr .center .snd

  -- invl : lsym ∙ q => counit
  -- comes from: lsym = divl counit, invl = lhtpy counit
  -- characterized by: fibroid q counit = Σ h, h ∙ q => counit
  J-invl : ∀ {ℓ} (P : (h : y ~> x) → h ∙ q => counit → Type ℓ)
         → P lsym invl
         → ∀ h α → P h α
  J-invl P base h α = subst (λ (h , α) → P h α) (unit-prop counit (lsym , invl) (h , α)) base

  invl-to-path : (h : y ~> x) → h ∙ q => counit → lsym ≡ h
  invl-to-path h α = ap fst (unit-prop counit (lsym , invl) (h , α))

  invr : q ∙ rsym => unit
  invr = rhtpy unit

  -- invr : q ∙ rsym => unit
  -- comes from: rsym = divr unit, invr = rhtpy unit
  -- characterized by: cofibroid q unit = Σ h, q ∙ h => unit
  invr-contr : is-contr (Σ h ∶ y ~> x , q ∙ h => unit)
  invr-contr = counit-equiv unit

  J-invr : ∀ {ℓ} (P : (h : y ~> x) → q ∙ h => unit → Type ℓ)
           → P rsym invr
           → ∀ h α → P h α
  J-invr P base h α = subst (λ (h , α) → P h α) (counit-prop unit (rsym , invr) (h , α)) base

  invr-to-path : (h : y ~> x) → q ∙ h => unit → rsym ≡ h
  invr-to-path h α = ap fst (counit-prop unit (rsym , invr) (h , α))

  -- fibroid q (rsym ∙ q) = Σ h : y ~> x, h ∙ q => rsym ∙ q
  -- Center: (rsym, crefl)

  -- J-rsym : (P : (h : y ~> y) → rsym ∙ q => h → Type)
  --          → P rsym invr
  --          → ∀ h α → P h α
  -- J-rsym P base h α = subst (λ (h , α) → P h α) (unit-prop (rsym ∙ q) (h , α) {!!}) {!!}

  midpoint : unit ∙ q => q ∙ counit
  midpoint = lift-path crefl (cat (to-path unitp) (sym (to-path counitp)))


record _≈_ {x y} (f g : x ~> y) : Type (u ⊔ v ⊔ w) where
  field
    arc : x ~> y
    iso : is-isomorphism arc
  private module iso = cocartesian arc iso
  field
    lcoh : f ∙ iso.counit => arc
    rcoh : iso.unit ∙ g => arc




-- module ≈-from-Iso {x y z : Ob} (q : y ~> z) (q-iso : is-isomorphism q) where
--   open cocartesian q q-iso

--   _≈_ : x ~> y → x ~> y → Type (v ⊔ w)
--   f ≈ g = Σ s ∶ x ~> z , (f ∙ q => s) × (g ∙ q => s)

--   -- From your J-counit pattern:
--   ≈-is-prop : {f g : x ~> y} → is-prop (f ≈ g)
--   ≈-is-prop {f} {g} (s , α , β) (s' , α' , β') =
--     let -- Use counit-prop: cofibroid q s is propositional
--         f0 : (s , α) ≡ (s' , α')
--         f0 = composites-prop (s , α) (s' , α')

--         f1 : {!!} ≡ {!!}
--         f1 = counit-prop {!!} {!!} {!!}

--         p0 : s ≡ s'
--         p0 = ap fst f0
--         p1 : PathP (λ i → {!Σ s ∶ x ~> z , (f ∙ q => ?) × (g ∙ q => ?)!}) (α , β) (α' , β')
--         p1 = {!ap snd p!}
--     in λ i → p0 i , {!p1 i!}

--   -- Transitivity uses the cocartesian structure
--   ≈-trans : {f g h : x ~> y} → f ≈ g → g ≈ h → f ≈ h
--   ≈-trans {f} {g} {h} (s , α , β) (t , γ , δ) =
--     -- Use eql-path to connect: since g ∙ q => s and g ∙ q => t, we get s => t
--     -- Then transport α along this
--     t , transport (λ i → f ∙ q => {!!}) α , δ



cocart-idem-unique : ∀ {x} (q q' : x ~> x)
                   → (cq : is-isomorphism q) (cq' : is-isomorphism q')
                   → (idem-q : q ∙ q => q)
                   → (let k = cq' .is-isomorphism.left q .center .fst
                          H = cq' .is-isomorphism.left q .center .snd)
                   → q' ∙ (q' ∙ k) => (q' ∙ k)
                   → q ≡ q'
cocart-idem-unique {x} q q' cq cq' idem-q lin = ap fst path module cocart-idem-unique where
  module iso = cocartesian q cq
  module iso' = cocartesian q' cq'

  k = iso'.divr q
  q'k=>q = iso'.rhtpy q

  -- The two key coherences from contractibility
  lin-coh : (q' ∙ k , lin) ≡ (k , crefl)
  lin-coh = iso'.counit-prop (q' ∙ k) _ _

  the-path : PathP (λ i → q' ∙ lin-coh i .fst => (q' ∙ k)) lin crefl
  the-path = ap snd lin-coh

  comp-coh : (q' ∙ k , crefl) ≡ (q , q'k=>q)
  comp-coh = composites-prop (_ , crefl) (_ , q'k=>q)

  k≡q'k : k ≡ q' ∙ k
  k≡q'k = sym (ap fst lin-coh)

  q'k≡q : q' ∙ k ≡ q
  q'k≡q = to-path q'k=>q

  k≡q : k ≡ q
  k≡q = cat k≡q'k q'k≡q

  -- Now transport q'k=>q along k≡q
  q'q=>q : q' ∙ q => q
  q'q=>q = transport (λ i → q' ∙ k≡q i => q) q'k=>q

  path : (q , idem-q) ≡ (q' , q'q=>q)
  path = iso.unit-prop q _ _

cocart-idem-unique' : ∀ {x} (q q' : x ~> x)
                    → (cq : is-isomorphism q) (cq' : is-isomorphism q')
                    → (idem-q : q ∙ q => q)
                    → (let k' = cq' .is-isomorphism.right q .center .fst)
                    → ((k' ∙ q') ∙ q') => (k' ∙ q')
                    → q ≡ q'
cocart-idem-unique' {x} q q' cq cq' idem-q thk =
    ap fst (is-contr→is-prop (cq .is-isomorphism.left q) (q , idem-q) (q' , qq'=>q))
    where
      module cq = is-isomorphism cq
      module cq' = is-isomorphism cq'

      -- Step 1: get k' with k' ∙ q' => q
      k' : x ~> x
      k' = cq'.right q .center .fst

      k'q'=>q : k' ∙ q' => q
      k'q'=>q = cq'.right q .center .snd

      -- Chain: q ∙ q' => (k' ∙ q') ∙ q' => k' ∙ q' => q
      qq'=>q : q ∙ q' => q
      qq'=>q = weak-vconcat (Overlap.lwhisk-op k'q'=>q) (weak-vconcat thk k'q'=>q)



-- cocart-idem-unique-alt : ∀ {x} (q q' : x ~> x)
--                    → (cq : is-isomorphism q) (cq' : is-isomorphism q')
--                    → (idem-q : q ∙ q => q)
--                    → (let k = cq' .is-isomorphism.left q .center .fst
--                           module k = cocartesian q' cq')
--                    → (lin : q' ∙ (q' ∙ k) => (q' ∙ k))
--                    → (q , idem-q) ≡ (q' , {!!})
-- cocart-idem-unique-alt {x} q q' cq cq' idem-q lin =
--   is-contr→is-prop (cq .is-isomorphism.right q) (q , idem-q) (q' , q'q=>q)
--     where
--       -- module cq = is-isomorphism cq
--       -- module cq' = is-isomorphism cq'

--       module cc = cocartesian q cq
--       module cc' = cocartesian q' cq'

--       -- Step 1: get k with q' ∙ k => q
--       k0 : x ~> x
--       k0 = cc'.divl q
--       k1 : x ~> x
--       k1 = cc'.divr q

--       q'k=>q : q' ∙ k1 => q
--       q'k=>q = cc'.rhtpy q

--       q'q=>q : q' ∙ q => q
--       q'q=>q = weak-vconcat (overlap-coh.rwhisk-op q'k=>q) (weak-vconcat lin q'k=>q)

--       counitp' : (q' ∙ cc'.counit) => q'
--       counitp' = cc'.counitp

--       unitp' : (cc'.unit ∙ q') => q'
--       unitp' = cc'.unitp

--       f0 : q' ∙ q ≡ q
--       f0 i = composites-prop (q' ∙ q , crefl) (q , q'q=>q) i .fst
```

Lets consider carefully...



`α : f => g`, then `mid` with `q : z ~> mid` known to be cocartesian.


linear :

```

2-prop : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
        → (α : f ∙ g => s) (β : f ∙ g => s')
        → (s , α) ≡ (s' , β)
2-prop α β = composites-prop (_ , α) (_ , β)

lower-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
         → f ∙ g => s → f ∙ g => s' → s ≡ s'
lower-path α β = ap fst (2-prop α β)

2-fibers : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
          → (α : f ∙ g => s)
          → hcenter ≡ (s , α)
2-fibers {f} {g} {s} α = 2-prop crefl α

2-op-fibers : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
          → (α : f ∙ g => s)
          → (s , α) ≡ hcenter
2-op-fibers {f} {g} {s} α = 2-prop α crefl

2-idem : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
       → (α : f ∙ g => s) (β : f ∙ g => s')
       → PathP (λ i → 2-fibers α (~ i) ≡ 2-fibers β (~ i)) (2-prop α β)
               (cat (erefl hcenter) (erefl hcenter))
2-idem {f} {g} {s} {s'} α β j i = hfill (∂ i) j λ where
    k (i = i0) → p (~ j)
    k (i = i1) → q (~ j)
    k (k = i0) → 2-prop crefl (path i .snd) (~ j) .fst , 2-prop crefl (path i .snd) (~ j) .snd
  where
  cc = composites-contr f g
  c = cc .center

  p = 2-fibers α
  q = 2-fibers β

  path : (s , α) ≡ (s' , β)
  path = composites-prop (s , α) (s' , β)

3-op-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
          → (α : f ∙ g => s)
          → 2-prop α crefl ≡ cat (erefl (s , α)) (2-op-fibers α)
3-op-path {f} {g} α =  is-contr→is-set (composites-contr f g) _ _ (2-prop α crefl) (cat refl (2-op-fibers α))

3-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
       → (α : f ∙ g => s)
       → 2-prop crefl α ≡ cat (2-fibers α) (erefl (s , α))
3-path {f} {g} α = is-contr→is-set (composites-contr f g) _ _ (2-prop crefl α) (cat (2-fibers α) refl)

3-coherence : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
            → (α : f ∙ g => s) (β : f ∙ g => s')
            → PathP (λ i → cat (2-fibers α) refl (~ i) ≡ cat (2-fibers β) refl (~ i))
                    (2-prop α β)
                    (erefl hcenter)
3-coherence {f} {g} α β i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → 2-prop α β j
  k (i = i1) → path-idem hcenter k j
  k (j = i0) → 3-path α k (~ i)
  k (j = i1) → 3-path β k (~ i)
  k (k = i0) → 2-idem α β i j

-- 3-op-coherence : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
--             → (α β : f ∙ g => s)
--             → PathP (λ i → cat refl (2-op-fibers α) (~ i) ≡ cat refl (2-op-fibers β) (~ i))
--                     (erefl hcenter)
--                     (2-prop α β)
-- 3-op-coherence {f} {g} α β i j = hcomp (∂ i ∨ ∂ j) λ where
--   k (i = i0) → {!3-op-path α !}
--   k (i = i1) → {!!}
--   k (j = i0) → {!3-op-path α k i !} -- 3-op-path α k (~ i)
--   k (j = i1) → {!i!}  -- 3-op-path β k (~ i)
--   k (k = i0) → 2-idem α β j i

-- module lin-thk-props {x y : Ob} (idn : x ~> x) (cc : is-isomorphism idn) where
--   private module iso = cocartesian idn cc

--   lin-is-prop : (f : x ~> y) → is-prop (idn ∙ (idn ∙ f) => idn ∙ f)
--   lin-is-prop f lin₁ lin₂ = goal where
--     C = iso.counit-equiv (idn ∙ f)
--     c = C .center
--     d = c .fst
--     r = c .snd  -- r : idn ∙ d => idn ∙ f

--     to₁ : c ≡ (idn ∙ f , lin₁)
--     to₁ = C .paths _

--     to₂ : c ≡ (idn ∙ f , lin₂)
--     to₂ = C .paths _

--     -- Paths in the hom type from center to idn ∙ f
--     p₁ : d ≡ idn ∙ f
--     p₁ = ap fst to₁

--     p₂ : d ≡ idn ∙ f
--     p₂ = ap fst to₂

--     -- Dependent paths from r to lin₁ and lin₂
--     r-to-lin₁ : PathP (λ i → idn ∙ p₁ i => idn ∙ f) r lin₁
--     r-to-lin₁ = ap snd to₁

--     r-to-lin₂ : PathP (λ i → idn ∙ p₂ i => idn ∙ f) r lin₂
--     r-to-lin₂ = ap snd to₂

--     -- Square in the hom type with corners at d
--     hom-sq : I → I → x ~> y
--     hom-sq i j = hfill (∂ i) j λ where
--       k (i = i0) → p₁ k
--       k (i = i1) → p₂ k
--       k (k = i0) → d

--     -- At j=1, hom-sq i i1 = idn ∙ f at both i=0 and i=1
--     -- (since p₁ i1 = p₂ i1 = idn ∙ f)

--     goal : lin₁ ≡ lin₂
--     goal i = {!!}

--   thk-is-prop : {w : Ob} (f : w ~> x) → is-prop ((f ∙ idn) ∙ idn => f ∙ idn)
--   thk-is-prop {w} f thk₁ thk₂ = goal where
--     C = iso.unit-equiv (f ∙ idn)
--     c = C .center
--     d = c .fst
--     r = c .snd  -- r : d ∙ idn => f ∙ idn

--     to₁ : c ≡ (f ∙ idn , thk₁)
--     to₁ = C .paths _

--     to₂ : c ≡ (f ∙ idn , thk₂)
--     to₂ = C .paths _

--     p₁ : d ≡ f ∙ idn
--     p₁ = ap fst to₁

--     p₂ : d ≡ f ∙ idn
--     p₂ = ap fst to₂

--     r-to-thk₁ : PathP (λ i → p₁ i ∙ idn => f ∙ idn) r thk₁
--     r-to-thk₁ = ap snd to₁

--     r-to-thk₂ : PathP (λ i → p₂ i ∙ idn => f ∙ idn) r thk₂
--     r-to-thk₂ = ap snd to₂

--     hom-sq : I → I → w ~> x
--     hom-sq i j = hfill (∂ i) j λ where
--       k (i = i0) → p₁ k
--       k (i = i1) → p₂ k
--       k (k = i0) → d

--     goal : thk₁ ≡ thk₂
--     goal i = {!!}
--     -- comp (λ j → hom-sq i j ∙ idn => f ∙ idn) (∂ i) λ where
--     --  j (i = i0) → r-to-thk₁ j
--     --  j (i = i1) → r-to-thk₂ j
--     --  j (j = i0) → ?



-- cocart-idem-unique' : ∀ {x} (q q' : x ~> x)
--                     → (cq : is-isomorphism q) (cq' : is-isomorphism q')
--                     → (idem-q : q ∙ q => q)
--                     → (let k' = cq' .is-isomorphism.right q .center .fst)
--                     → (thk : (k' ∙ q') ∙ q' => k' ∙ q')
--                     → q ≡ q'
-- cocart-idem-unique' {x} q q' cq cq' idem-q thk = ap fst path where
--   module iso = cocartesian q cq
--   module iso' = cocartesian q' cq'

--   k' = iso'.divl q
--   k'q'=>q = iso'.lhtpy q

--   -- The two key coherences from contractibility
--   thk-coh : (k' ∙ q' , thk) ≡ (k' , crefl)
--   thk-coh = iso'.unit-prop (k' ∙ q') _ _

--   comp-coh : (k' ∙ q' , crefl) ≡ (q , k'q'=>q)
--   comp-coh = 2-prop crefl k'q'=>q

--   -- k' acts as right identity absorbed by q' (from thk-coh)
--   -- and k' ∙ q' = q (from k'q'=>q)
--   -- So k' = k' ∙ q' = q

--   k'≡k'q' : k' ≡ k' ∙ q'
--   k'≡k'q' = sym (ap fst thk-coh)

--   k'q'≡q : k' ∙ q' ≡ q
--   k'q'≡q = to-path k'q'=>q

--   k'≡q : k' ≡ q
--   k'≡q = cat k'≡k'q' k'q'≡q

--   -- Now transport k'q'=>q along k'≡q
--   qq'=>q : q ∙ q' => q
--   qq'=>q = transport (λ i → k'≡q i ∙ q' => q) k'q'=>q

--   path : (q , idem-q) ≡ (q' , qq'=>q)
--   path = iso.counit-prop q _ _

-- record has-unit x : Type (u ⊔ v ⊔ w) where
--   field
--     idn : x ~> x
--     iso : is-isomorphism idn
--     lin : ∀ {y} (f : x ~> y) → idn ∙ (idn ∙ f) => idn ∙ f

-- module has-unit-lemmas {x : Ob} (hu : has-unit x) where
--   private module hu = has-unit hu
--   private module iso = cocartesian hu.idn hu.iso

--   idn : x ~> x
--   idn = hu.idn

--   -- The key coherence: (idn ∙ f, lin f) and (f, crefl) are both in cofibroid idn (idn ∙ f)
--   lin-coh : ∀ {y} (f : x ~> y) → (idn ∙ f , hu.lin f) ≡ (f , crefl)
--   lin-coh f = iso.counit-prop (idn ∙ f) _ _

--   unitl-comp : ∀ {y} (f : x ~> y) → idn ∙ f ≡ f
--   unitl-comp f = ap fst (lin-coh f)

--   -- The PathP from lin-coh directly gives the 2-cell structure
--   unitl-pathp : ∀ {y} (f : x ~> y) → PathP (λ i → idn ∙ unitl-comp f i => idn ∙ f) (hu.lin f) crefl
--   unitl-pathp f = ap snd (lin-coh f)

--   unitl : ∀ {y} (f : x ~> y) → idn ∙ f => f
--   unitl f = subst (idn ∙ f =>_) (unitl-comp f) crefl

--   idem : idn ∙ idn => idn
--   idem = unitl idn

--   -- To show idn = iso.counit, use that both (idn, counitp) and (iso.counit, unitl iso.counit)
--   -- live in the contractible Σ s, idn ∙ iso.counit => s
--   counit-coh : (idn , iso.counitp) ≡ (iso.counit , unitl iso.counit)
--   counit-coh = composites-prop _ _

--   idn-is-counit : idn ≡ iso.counit
--   idn-is-counit = ap fst counit-coh

--   -- counit-path via the PathP from counit-coh
--   counit-pathp : PathP (λ i → idn ∙ iso.counit => idn-is-counit i) iso.counitp (unitl iso.counit)
--   counit-pathp = ap snd counit-coh

--   -- For lsym-idn, we need idn in fibroid idn iso.counit = Σ h, h ∙ idn => iso.counit
--   -- We have idem : idn ∙ idn => idn, and idn-is-counit : idn = iso.counit
--   -- So we need: idn ∙ idn => iso.counit
--   idn-counit : fibroid idn iso.counit
--   idn-counit = idn , transport (λ i → (idn ∙ idn) => unitl-comp (idn-is-counit i) i) crefl

--   lsym-idn : iso.lsym ≡ idn
--   lsym-idn = ap fst (iso.lpaths iso.counit idn-counit)

-- record has-counit x : Type (u ⊔ v ⊔ w) where
--   field
--     idn : x ~> x
--     iso : is-isomorphism idn
--     thk : ∀ {w} (f : w ~> x) → (f ∙ idn) ∙ idn => f ∙ idn

-- module has-counit-lemmas {x : Ob} (co : has-counit x) where
--   private module co = has-counit co
--   private module iso = cocartesian co.idn co.iso

--   idn : x ~> x
--   idn = co.idn

--   -- Dual coherence from cocartesian structure
--   thk-coh : ∀ {w} (f : w ~> x) → (f ∙ idn , co.thk f) ≡ (f , crefl)
--   thk-coh f = iso.unit-prop (f ∙ idn) _ _

--   unitr-comp : ∀ {w} (f : w ~> x) → f ∙ idn ≡ f
--   unitr-comp f = ap fst (thk-coh f)

--   unitr-pathp : ∀ {w} (f : w ~> x) → PathP (λ i → unitr-comp f i ∙ idn => f ∙ idn) (co.thk f) crefl
--   unitr-pathp f = ap snd (thk-coh f)

--   unitr : ∀ {w} (f : w ~> x) → f ∙ idn => f
--   unitr f = transport (λ i → (f ∙ co.idn) => unitr-comp f i) crefl

--   idem : idn ∙ idn => idn
--   idem = unitr idn

--   -- Dual: show idn = iso.unit
--   unit-coh : (idn , iso.unitp) ≡ (iso.unit , unitr iso.unit)
--   unit-coh = composites-prop _ _

--   idn-is-unit : idn ≡ iso.unit
--   idn-is-unit = ap fst unit-coh

--   unit-pathp : PathP (λ i → (iso.unit ∙ co.idn) => idn-is-unit i) iso.unitp (unitr iso.unit)
--   unit-pathp = ap snd unit-coh

--   -- For rsym-idn, we need idn in cofibroid idn iso.unit = Σ h, idn ∙ h => iso.unit
--   idn-unit : cofibroid idn iso.unit
--   idn-unit = idn , transport (λ i → (idn ∙ idn) => unitr-comp (idn-is-unit i) i) crefl

--   rsym-idn : iso.rsym ≡ idn
--   rsym-idn = ap fst (iso.rpaths iso.unit idn-unit)

-- has-unit-is-prop : ∀ {x} → is-prop (has-unit x)
-- has-unit-is-prop {x} u u' = path where
--   module u = has-unit u
--   module u' = has-unit u'
--   module iso = cocartesian u.idn u.iso
--   module iso' = cocartesian u'.idn u'.iso
--   module ul = has-unit-lemmas u
--   module ul' = has-unit-lemmas u'

--   -- Get idn-path from cocart-idem-unique
--   k : x ~> x
--   k = iso'.counit-equiv u.idn .center .fst

--   idn-path : u.idn ≡ u'.idn
--   idn-path = cocart-idem-unique u.idn u'.idn u.iso u'.iso ul.idem (u'.lin k)

--   iso-path : PathP (λ i → is-isomorphism (idn-path i)) u.iso u'.iso
--   iso-path = is-prop→PathP (λ i → is-isomorphism-is-prop (idn-path i)) u.iso u'.iso

--   lin-path : PathP (λ i → ∀ {y} (f : x ~> y) → idn-path i ∙ (idn-path i ∙ f) => idn-path i ∙ f) u.lin u'.lin
--   lin-path i {y} f = {!!}
--     where
--       -- The cofibroid type along the path
--       Cofib : I → Type _
--       Cofib i = Σ h ∶ (x ~> y) , (idn-path i) ∙ h => (idn-path i) ∙ f

--       -- It's a prop at each i, via the transported cocartesian structure
--       cofib-is-prop : (i : I) → is-prop (Cofib i)
--       cofib-is-prop i = cocartesian.counit-prop (idn-path i) (iso-path i) ((idn-path i) ∙ f)

--       -- The two endpoints in the respective cofibroids
--       endpoint₀ : Cofib i0
--       endpoint₀ = (u.idn ∙ f , u.lin f)

--       endpoint₁ : Cofib i1
--       endpoint₁ = (u'.idn ∙ f , u'.lin f)

--       -- PathP in the total type (via is-prop→PathP)
--       cofib-pathp : PathP Cofib endpoint₀ endpoint₁
--       cofib-pathp = is-prop→PathP cofib-is-prop endpoint₀ endpoint₁

--   path : u ≡ u'
--   path i = record { idn = idn-path i ; iso = iso-path i ; lin = lin-path i }

-- is-isomorphism→is-linear-is-prop : ∀ {x y} (idn : x ~> x) (cc : is-isomorphism idn)
--                                  → (f : x ~> y) → is-prop (idn ∙ idn ∙ f => idn ∙ f)
-- is-isomorphism→is-linear-is-prop {x} {y} idn cc f α β = goal where
--   module iso = cocartesian idn cc

--   C : is-contr (cofibroid idn (idn ∙ f))
--   C = iso.counit-equiv (idn ∙ f)

--   -- The total space is a set (contractible → prop → set)
--   C-is-set : is-set (cofibroid idn (idn ∙ f))
--   C-is-set = is-contr→is-set C

--   -- Path in the total space from contractibility
--   total-path : (idn ∙ f , α) ≡ (idn ∙ f , β)
--   total-path = is-contr→is-prop C _ _

--   -- First component is a loop at idn ∙ f
--   fst-loop : idn ∙ f ≡ idn ∙ f
--   fst-loop = ap fst total-path

--   -- The second component gives a PathP over fst-loop
--   snd-pathp : PathP (λ i → idn ∙ fst-loop i => idn ∙ f) α β
--   snd-pathp i = total-path i .snd

--   -- Transport along fst-loop-is-refl to get a path over refl, i.e., α ≡ β
--   goal : α ≡ β
--   goal = subst (λ p → PathP (λ i → idn ∙ p i => idn ∙ f) α β) {!!} snd-pathp

-- has-unit-is-prop : ∀ {x} → is-prop (has-unit x)
-- has-unit-is-prop {x} u u' = path module has-unit-is-prop where
--   private module u = has-unit u
--   private module u' = has-unit u'
--   private module iso = cocartesian u.idn u.iso
--   private module iso' = cocartesian u'.idn u'.iso

--   counit-prop = iso.counit-prop
--   counit-prop' = iso'.counit-prop

--   -- Derive idem from lin via the unitl-comp construction
--   lin-coh : ∀ {y} (f : x ~> y) → (u.idn ∙ f , u.lin f) ≡ (f , crefl)
--   lin-coh f = counit-prop (u.idn ∙ f) _ _

--   -- Derive idem from lin via the unitl-comp construction
--   lin'-coh : ∀ {y} (f : x ~> y) → (u'.idn ∙ f , u'.lin f) ≡ (f , crefl)
--   lin'-coh f = counit-prop' (u'.idn ∙ f) _ _

--   unitl-comp : ∀ {y} (f : x ~> y) → u.idn ∙ f ≡ f
--   unitl-comp f = ap fst (lin-coh f)

--   unitl-comp' : ∀ {y} (f : x ~> y) → u'.idn ∙ f ≡ f
--   unitl-comp' f = ap fst (lin'-coh f)

--   idem : u.idn ∙ u.idn => u.idn
--   idem = subst (u.idn ∙ u.idn =>_) (unitl-comp u.idn) crefl

--   private
--     -- k from u'.iso for cocart-idem-unique
--     k : x ~> x
--     k = iso'.counit-equiv u.idn .center .fst

--   -- u'.lin k gives exactly the assoc data needed
--   idn-path : u.idn ≡ u'.idn
--   idn-path = cocart-idem-unique u.idn u'.idn u.iso u'.iso idem (u'.lin k)

--   idn-path' : u.idn ≡ u'.idn
--   idn-path' = cat (sym (unitl-comp u.idn)) (cat {!!} (unitl-comp u'.idn))

--   _ : ∀ {y} (f : x ~> y) → {!!}
--   _ = λ f → counit-prop (u.idn ∙ f) (u.idn ∙ f , u.lin f) (u'.idn ∙ f , weak-vconcat {!!} (u.lin f))

--   -- iso fields match by is-isomorphism-is-prop
--   iso-path : PathP (λ i → is-isomorphism (idn-path i)) u.iso u'.iso
--   iso-path = is-prop→PathP (λ i → is-isomorphism-is-prop (idn-path i)) u.iso u'.iso

--   lin-path' : PathP (λ i → ∀ {y} (f : x ~> y) → idn-path i ∙ (idn-path i ∙ f) => idn-path i ∙ f) u.lin u'.lin
--   lin-path' i {y} f = {!!}
--     where
--       -- Dependent family of contractible types
--       C : (j : I) → is-contr (cofibroid (idn-path j) (idn-path j ∙ f))
--       C j = cocartesian.counit-equiv (idn-path j) (iso-path j) (idn-path j ∙ f)

--       -- Contraction paths to (f, crefl) at endpoints
--       p0 : (u.idn ∙ f , u.lin f) ≡ (f , crefl)
--       p0 = iso.counit-prop (u.idn ∙ f) _ _

--       p1 : (u'.idn ∙ f , u'.lin f) ≡ (f , crefl)
--       p1 = iso'.counit-prop (u'.idn ∙ f) _ _

--       -- Fill the square using (f, crefl) as the floor
--       sq : I → I → cofibroid (idn-path i) (idn-path i ∙ f)
--       sq j k = hfill (∂ j) k λ where
--         l (j = i0) → {!!}
--         l (j = i1) → {!!}
--         l (l = i0) → (f , crefl)

--   -- lin f is propositional: it's a fiber of fst over a contractible type
--   -- cofibroid (idn-path i) (idn-path i ∙ f) is contractible
--   -- so fiber over (idn-path i ∙ f) is contractible when inhabited
--   lin-path : ∀ {y} (f : x ~> y) → PathP (λ i → (idn-path i ∙ idn-path i ∙ f) => (idn-path i ∙ f)) (u.lin f) (u'.lin f) -- PathP (λ i → ∀ {y} (f : x ~> y) → idn-path i ∙ (idn-path i ∙ f) => idn-path i ∙ f) u.lin u'.lin
--   lin-path {y} f i = {!!}
--     where
--     lin-coh0 : (u.idn ∙ f , u.lin f) ≡ (f , crefl)
--     lin-coh0 = iso.counit-prop (u.idn ∙ f) _ _

--     lin-coh1 : (u'.idn ∙ f , u'.lin f) ≡ (f , crefl)
--     lin-coh1 = iso'.counit-prop (u'.idn ∙ f) _ _

--     crefl-path : PathP (λ i → cofibroid (idn-path i) (idn-path i ∙ f)) (f , crefl) (f , crefl)
--     crefl-path i = (f , crefl)

--     total-path : PathP (λ i → cofibroid (idn-path i) (idn-path i ∙ f)) (u.idn ∙ f , u.lin f) (u'.idn ∙ f , u'.lin f)
--     total-path i = comp (λ j → cofibroid (idn-path i) (idn-path i ∙ f)) (∂ i) λ where
--       j (i = i0) → lin-coh0 (~ j)
--       j (i = i1) → lin-coh1 (~ j)
--       j (j = i0) → crefl-path i

--   path : u ≡ u'
--   path i .has-unit.idn = idn-path i
--   path i .has-unit.iso = iso-path i
--   path i .has-unit.lin f = {!!} -- lin-path i

-- has-counit-is-prop : ∀ {x} → is-prop (has-counit x)
-- has-counit-is-prop {x} c c' = path where
--   module c = has-counit c
--   module c' = has-counit c'
--   module iso = cocartesian c.idn c.iso
--   module iso' = cocartesian c'.idn c'.iso

--   thk-coh : ∀ {w} (f : w ~> x) → (f , crefl) ≡ (f ∙ c.idn , c.thk f)
--   thk-coh f = is-contr→is-prop (iso.unit-equiv (f ∙ c.idn)) _ _

--   unitr-comp : c.idn ∙ c.idn ≡ c.idn
--   unitr-comp = sym (ap fst (thk-coh c.idn))

--   idem : c.idn ∙ c.idn => c.idn
--   idem = subst (c.idn ∙ c.idn =>_) unitr-comp (crefl)

--   k' : x ~> x
--   k' = iso'.unit-equiv c.idn .center .fst

--   idn-path : c.idn ≡ c'.idn
--   idn-path = cocart-idem-unique' c.idn c'.idn c.iso c'.iso idem (c'.thk k')

--   iso-path : PathP (λ i → is-isomorphism (idn-path i)) c.iso c'.iso
--   iso-path = is-prop→PathP (λ i → is-isomorphism-is-prop (idn-path i)) c.iso c'.iso

--   thk-path : PathP (λ i → ∀ {w} (f : w ~> x) → (f ∙ idn-path i) ∙ idn-path i => f ∙ idn-path i) c.thk c'.thk
--   thk-path = {!!} -- is-prop→PathP (λ i → implicit-Π-is-prop λ w → Π-is-prop λ f →
--     --fiber-of-contr-is-prop (cocartesian.unit-equiv (idn-path i) (iso-path i) (f ∙ idn-path i))) c.thk c'.thk

--   path : c ≡ c'
--   path i .has-counit.idn = idn-path i
--   path i .has-counit.iso = iso-path i
--   path i .has-counit.thk = thk-path i
--   --record { idn = idn-path i ; iso = iso-path i ; thk = thk-path i }
```
record is-displayed-graph {u v} w z (G : Graph u v) : Type (u ⊔ v ⊔ (w ⊔ z) ₊) where
  private
    module G = Graph G
    _~>_ = G.₁; infix 4 _~>_

  ₀ = G.₀
  ₁ = G.₁

  field
    Ob : ₀ → Type w
    Edge : ∀ {x y} → x ~> y → Ob x → Ob y → Type z

record is-eqv-graph {u v} (G : Graph u v) (D : is-displayed-graph v v G) : Type (u ⊔ v) where
  private
    module G = Graph G
    module D = is-displayed-graph D
    ob = G.₀
    _~>_ = G.₁; infix 4 _~>_

  _≈[_]_ : ∀ {x y} → D.Ob x → x ~> y → D.Ob y → Type v
  _≈[_]_ f a = D.Edge a f

  field
    ctr : ∀ {x} → D.Ob x
    eqv : ∀ {x y} {a : D.Ob x} {s : x ~> y} → a ≈[ s ] ctr
    prop : ∀ {x y} {a : D.Ob x} → is-prop (Σ b ∶ D.Ob y , Σ s ∶ x ~> y , a ≈[ s ] b)

  -- prop : ∀ {x y} {a : D.Ob x} ?

  ecenter : ∀ {x y} {s : x ~> y} → Σ a ∶ D.Ob x ,  Σ s ∶ x ~> y , a ≈[ s ] ctr
  ecenter {s} = ctr , s , eqv

  to-path : ∀ {x y} {a : D.Ob x} {b b' : D.Ob y} {s s' : x ~> y}
          → a ≈[ s ] b → a ≈[ s' ] b'
          → b ≡ b'
  to-path α β = ap fst (prop (_ , _ , α) (_ , _ , β))

  to-path-over : ∀ {x y} {a : D.Ob x} {b b' : D.Ob y} {s s' : x ~> y}
          → a ≈[ s ] b → a ≈[ s' ] b'
          → s ≡ s'
  to-path-over α β = ap (λ z → fst (snd z)) (prop (_ , _ , α) (_ , _ , β))

  to-pathp : ∀ {x y} {a : D.Ob x} {b b' : D.Ob y} {s s' : x ~> y}
           → (α : a ≈[ s ] b) (β : a ≈[ s' ] b')
           → PathP (λ i → a ≈[ to-path-over α β i ] to-path α β i) α β
  to-pathp α β = ap (λ z → snd (snd z)) (prop (_ , _ , α) (_ , _ , β))
