```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Graph.Virtual.Base where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Core.Kan using (hcomp; hfill; transport-filler)
open import Lib.Path hiding (to-path; to-path-over)
open import Lib.Equal hiding (_∙_; _⨾_)
open import Lib.Graph
open import Lib.Underlying

record is-virtual-graph {u v} w (G : Graph u v) : Type (u ⊔ v ⊔ w ₊) where
  no-eta-equality
  private module G = Graph G; _~>_ = G.₁
  field
    ₂ : ∀ {x y} → x ~> y → x ~> y → Type w
    concat : ∀ {x y z} → x ~> y → y ~> z → x ~> z
  private _=>_ = ₂; _∙_ = concat; infixr 40 _∙_
  field
    hrefl : ∀ {x y z} {f : x ~> y} {g : y ~> z} → concat f g => concat f g
    composites-prop : ∀ {x y z} {f : x ~> y} {g : y ~> z}
                      → is-prop (Σ s ∶ (x ~> z) , concat f g => s)
    hconcat : {x y z : G.₀} {e1 d1 : x ~> y} {e2 d2 : y ~> z}
            → e1 => d1 → e2 => d2 → (concat e1 e2) => (concat d1 d2)
    vconcat : ∀ {x y} {f g h : x ~> y} → f => g → g => h → f => h

V-graph : (u v w : Level) → Type₊ (u ⊔ v ⊔ w)
V-graph u v w = Σ G ∶ Graph u v , is-virtual-graph w G

module V-graph {u v w} ((G , V) : V-graph u v w) where
  open Graph G renaming (₀ to Ob; ₁ to infix 4 _~>_)
  private
    module V = is-virtual-graph V
    _∙_ = V.concat
    _=>_ = V.₂

    _⊚_ = V.vconcat
    infixr 40 _∙_ _⊚_
  ₀ = Ob
  ₁ = _~>_
  ₂ = _=>_

  concat = V.concat
  vconcat = V.vconcat
  hrefl = V.hrefl
  composites-prop = V.composites-prop

  hcenter : ∀ {x y z} {f : x ~> y} {g : y ~> z} → Σ s ∶ (x ~> z) , f ∙ g => s
  hcenter {f} {g} = f ∙ g , hrefl

  to-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
          → f ∙ g => s → f ∙ g ＝ s
  to-path p i = composites-prop (_ , hrefl) (_ , p) i .fst

  to-pathp : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
           → (p : f ∙ g => s) → PathP (λ i → (f ∙ g) => to-path p i) hrefl p
  to-pathp p i = composites-prop (_ , hrefl) (_ , p) i .snd

  loop : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z} → f ∙ g => s → s => s
  loop {s} = λ α → transport (λ i → to-path α i => s) α

  lift-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {r s : x ~> z}
            → f ∙ g => r → r ＝ s →  r => s
  lift-path {r} {s} α p = transport (λ i → r => p i) (loop α)

  eql-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {r s : x ~> z}
            → f ∙ g => r → f ∙ g => s → r => s
  eql-path f g = lift-path f (cat (sym (to-path f)) (to-path g))

  module encode-decode {x y z} {f : x ~> y} {g : y ~> z} where
    encode : ∀ {s} → f ∙ g ≡ s → f ∙ g => s
    encode p = subst (f ∙ g =>_) p hrefl

    decode : ∀ {s} → f ∙ g => s → f ∙ g ≡ s
    decode = to-path

    -- The key fillers for the equivalence
    encode-filler : ∀ {s} (p : f ∙ g ≡ s)
                  → PathP (λ i → f ∙ g => p i) hrefl (encode p)
    encode-filler p = transport-filler (λ i → f ∙ g => p i) hrefl

  module _ {w x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z} (h : w ~> x) where
    apl : f ∙ g => s → h ∙ f ∙ g => h ∙ s
    apl α = transport (λ i → (h ∙ (f ∙ g)) => (h ∙ to-path α i)) hrefl

    apl-filler : (α : f ∙ g => s) → PathP (λ i → (h ∙ (f ∙ g)) => (h ∙ to-path α i)) hrefl (apl α)
    apl-filler α = transport-filler (λ i → (h ∙ (f ∙ g)) => (h ∙ to-path α i)) hrefl

    apl-prop : (α : f ∙ g => s)
             → (γ : h ∙ (f ∙ g) => h ∙ s)  -- any lift
             → (h ∙ s , apl α) ≡ (h ∙ s , γ)
    apl-prop α γ = composites-prop _ _

  module _ {w x y z} {f : w ~> x} {g : x ~> y} {s : w ~> y} (h : y ~> z) where
    apr : f ∙ g => s → (f ∙ g) ∙ h => s ∙ h
    apr α = transport (λ i → (f ∙ g) ∙ h => to-path α i ∙ h) hrefl

    apr-filler : (α : f ∙ g => s) → PathP (λ i → (f ∙ g) ∙ h => to-path α i ∙ h) hrefl (apr  α)
    apr-filler α = transport-filler (λ i → (f ∙ g) ∙ h => to-path α i ∙ h) hrefl

    apr-prop : (α : f ∙ g => s)
             → (γ : (f ∙ g) ∙ h => s ∙ h)
             → (s ∙ h , apr α) ≡ (s ∙ h , γ)
    apr-prop α γ = composites-prop _ _

  composites-contr : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-contr (Σ s ∶ x ~> z , f ∙ g => s)
  composites-contr f g .center = _ , hrefl
  composites-contr f g .paths x i = to-path (x .snd) i , to-pathp (x .snd) i

  J-composite : ∀ {x y z} {f : x ~> y} {g : y ~> z}
              → (P : (s : x ~> z) (α : f ∙ g => s) → Type)
              → P (f ∙ g) hrefl
              → (s : x ~> z) (α : f ∙ g => s) → P s α
  J-composite P base s α = transport (λ i → P (to-path α i) (to-pathp α i)) base

  weak-hsym : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
            → f ∙ g => s → s => f ∙ g
  weak-hsym {s} α = subst (s =>_) (sym (to-path α)) (loop α)

  weak-vconcat : ∀ {w x y z} {f : w ~> x} {f' : x ~> z} {g : w ~> y} {g' : y ~> z} {s : w ~> z}
               → f ∙ f' => g ∙ g' → g ∙ g' => s → f ∙ f' => s
  weak-vconcat {f} {f'} H K = subst (f ∙ f' =>_) (to-path K) H

  module overlap-coh {w x y z} {f : w ~> x} {g : x ~> y} {h : y ~> z} where
    lwhisk :  {s : w ~> y} → f ∙ g => s → (f ∙ g) ∙ h => s ∙ h
    lwhisk H = transport (λ i → (f ∙ g) ∙ h => to-path H i ∙ h) hrefl

    lwhisk-op : {s : w ~> y} → f ∙ g => s → s ∙ h => (f ∙ g) ∙ h
    lwhisk-op H = transport (λ i → to-path H i ∙ h => (f ∙ g) ∙ h) hrefl

    -- Abstract right overlap on target bracket
    rwhisk :  {r : x ~> z} → g ∙ h => r → f ∙ (g ∙ h) => f ∙ r
    rwhisk K = transport (λ i → f ∙ (g ∙ h) => f ∙ to-path K i) hrefl

    rwhisk-op : {r : x ~> z} → g ∙ h => r → f ∙ r => f ∙ (g ∙ h)
    rwhisk-op K = transport (λ i → f ∙ to-path K i => f ∙ (g ∙ h)) hrefl

    conj : {s : w ~> y} {r : x ~> z} → (f ∙ g) ∙ h => f ∙ (g ∙ h) → f ∙ g => s → g ∙ h => r → s ∙ h => f ∙ r
    conj A H K = subst2 (λ u v → u ∙ h => f ∙ v) (to-path H) (to-path K) A

    lcross : {s : w ~> y} → (f ∙ g) ∙ h => f ∙ (g ∙ h) → f ∙ g => s → s ∙ h => f ∙ (g ∙ h)
    lcross A H = subst (λ u → u ∙ h => f ∙ (g ∙ h)) (to-path H) A

    -- Keep left concrete, abstract right
    rcross : {r : x ~> z} → (f ∙ g) ∙ h => f ∙ (g ∙ h) → g ∙ h => r → (f ∙ g) ∙ h => f ∙ r
    rcross A K = subst (λ v → (f ∙ g) ∙ h => f ∙ v) (to-path K) A

  cofibroid : {x y z : Ob} → x ~> y → x ~> z → Type (v ⊔ w)
  cofibroid {y = y} {z} f s = Σ h ∶ y ~> z , f ∙ h => s

  fibroid : {a x y : Ob} → x ~> y → a ~> y → Type (v ⊔ w)
  fibroid {a} {x} f s = Σ h ∶ a ~> x , h ∙ f => s

  has-path : {x y z : Ob} → x ~> y → y ~> z → Type (v ⊔ w)
  has-path {x} {z} f g = Σ h ∶ x ~> z , f ∙ g => h


```
fibre-paths : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {y : B}
            → {f1 f2 : fibre f y}
            → (f1 ≡ f2)
            ≃ (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (ap f γ ∙ f2 .snd ≡ f1 .snd))

{f1 f2 : fibroid q s}
            → (f1 ≈ f2)
            ≃ (is-contr (Σ[ γ ∈ f1 .fst => f2 .fst ] (apl q γ ∙ f2 .snd ≈ f1 .snd)))

fibr-paths : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {y : B}
            → {f1 f2 : fibre f y}
            → (f1 ≡ f2)
            ≃ (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (ap f γ ∙ f2 .snd ≡ f1 .snd))

```

  -- record is-unital {x} (i : x ~> x) : Type (u ⊔ v ⊔ w) where
  --   field
  --     unit : ∀ {y} (f : x ~> y) → i ∙ f => f
  --     counit : ∀ {w} (f : x ~> y) → i ∙ f => f
  --     adj : ∀ {y} (f : x ~> y) → unit f ＝ counit f

  -- _≈_ : ∀ {x y} → (f g : x ~> y) → Type (u ⊔ v ⊔ w)
  -- _≈_ {x} {y} f g = Σ q ∶ x ~> y
  --                 , Σ M ∶ is-cocartesian q
  --                 , section M × retraction M × lin M × thk M
  --    where module _ {q : x ~> y} (cc : is-cocartesian q) where
  --      open cocartesian q cc

  --      retraction = f ∙ counit => q
  --      section = unit ∙ g => q
  --      lin = (unit ∙ unit) ∙ g => unit ∙ g
  --      thk = f ∙ (counit ∙ counit) => f ∙ counit


-- record is-unital (x : Ob) : Type (u ⊔ v) where
--   field
--     idn : x ~> x
--     iso : is-cocartesian idn
--     thk : {w : Ob} (f : w ~> x) → ((f ∙ idn) ∙ idn) => (f ∙ idn)
--     lin : {y : Ob} (f : x ~> y) → (idn ∙ (idn ∙ f)) => (idn ∙ f)

```
  module pentagon-coh {v w x y z} {f : v ~> w} {g : w ~> x} {h : x ~> y} {k : y ~> z}
    (α₁ : (f ∙ g) ∙ h => f ∙ (g ∙ h))           -- (f, g, h)
    (α₂ : (g ∙ h) ∙ k => g ∙ (h ∙ k))           -- (g, h, k)
    (α₃ : ((f ∙ g) ∙ h) ∙ k => (f ∙ g) ∙ (h ∙ k))  -- (f∙g, h, k)
    (α₄ : (f ∙ (g ∙ h)) ∙ k => f ∙ ((g ∙ h) ∙ k))  -- (f, g∙h, k)
    (α₅ : (f ∙ g) ∙ (h ∙ k) => f ∙ (g ∙ (h ∙ k)))  -- (f, g, h∙k) ← NEW
    where
    edge1 : ((f ∙ g) ∙ h) ∙ k => (f ∙ (g ∙ h)) ∙ k
    edge1 = overlap-coh.lwhisk α₁

    edge2 : (f ∙ (g ∙ h)) ∙ k => f ∙ ((g ∙ h) ∙ k)
    edge2 = α₄

    edge3 : ((f ∙ g) ∙ h) ∙ k => (f ∙ g) ∙ (h ∙ k)
    edge3 = α₃

    edge4 : (f ∙ g) ∙ (h ∙ k) => f ∙ (g ∙ (h ∙ k))
    edge4 = α₅

    edge5 : f ∙ ((g ∙ h) ∙ k) => f ∙ (g ∙ (h ∙ k))
    edge5 = overlap-coh.rwhisk α₂

    -- -- Pentagon identity: edge1 ⨾ edge2 ⨾ edge5 ＝ edge3 ⨾ edge4
    -- -- By 2-cell-prop, automatic!
    -- pentagon : edge1 ⨾ edge2 ⨾ edge5 ＝ edge3 ⨾ edge4
    -- pentagon = composites-prop _ _

    edge1-2 : ((f ∙ g) ∙ h) ∙ k => f ∙ ((g ∙ h) ∙ k)
    edge1-2 = weak-vconcat edge1 edge2

    top-path : ((f ∙ g) ∙ h) ∙ k => f ∙ (g ∙ (h ∙ k))
    top-path = weak-vconcat edge1-2 edge5

    -- Bottom path: V1 → V5 → V4
    -- V5 = (f ∙ g) ∙ (h ∙ k)  ← composite!

    bot-path : ((f ∙ g) ∙ h) ∙ k => f ∙ (g ∙ (h ∙ k))
    bot-path = weak-vconcat edge3 edge4

    -- Pentagon identity: both paths are equal
    -- V1 is a composite: ((f ∙ g) ∙ h) ∙ k
    -- So by composites-prop, any two 2-cells from V1 to the same target are equal!

    -- pentagon : top-path ＝ bot-path
    -- pentagon i = {!!} where
    --   module strict = strict-composites

  module pentagon-coh' {v w x y z} {f : v ~> w} {g : w ~> x} {h : x ~> y} {k : y ~> z}
    (α : ∀ {a b c d} (p : a ~> b) (q : b ~> c) (r : c ~> d) → (p ∙ q) ∙ r => p ∙ (q ∙ r))
    where

    edge1 : ((f ∙ g) ∙ h) ∙ k => (f ∙ (g ∙ h)) ∙ k
    edge1 = overlap-coh.lwhisk (α f g h)

    edge2 : (f ∙ (g ∙ h)) ∙ k => f ∙ ((g ∙ h) ∙ k)
    edge2 = α f (g ∙ h) k

    edge3 : ((f ∙ g) ∙ h) ∙ k => (f ∙ g) ∙ (h ∙ k)
    edge3 = α (f ∙ g) h k

    edge4 : (f ∙ g) ∙ (h ∙ k) => f ∙ (g ∙ (h ∙ k))
    edge4 = α f g (h ∙ k)

    edge5 : f ∙ ((g ∙ h) ∙ k) => f ∙ (g ∙ (h ∙ k))
    edge5 = overlap-coh.rwhisk (α g h k)

  module weak-core {x y z u v} {f : x ~> u} {g : u ~> y} {h : y ~> v} {k : v ~> z}
     where
    hconcat : {s1 : x ~> y} {s2 : y ~> z}
            → f ∙ g => s1
            → h ∙ k => s2
            → (f ∙ g) ∙ h ∙ k => s1 ∙ s2
    hconcat H K =
      transport (λ i → (f ∙ g) ∙ (h ∙ k) => (to-path H i ∙ to-path K i)) hrefl

    lwhisker : {s1 : x ~> y} → f ∙ g => s1 → (f ∙ g) ∙ (h ∙ k) => s1 ∙ (h ∙ k)
    lwhisker H = transport (λ i → ((f ∙ g) ∙ (h ∙ k)) => ((to-path H i) ∙ (h ∙ k))) hrefl

    rwhisker : {s2 : y ~> z} → h ∙ k => s2 → (f ∙ g) ∙ (h ∙ k) => (f ∙ g) ∙ s2
    rwhisker H = transport (λ i → ((f ∙ g) ∙ (h ∙ k)) => ((f ∙ g) ∙ (to-path H i))) hrefl

    assoc : {s1 : x ~> y} {s2 : y ~> z}
          → f ∙ g => s1
          → h ∙ k => s2
          → s1 ∙ h ∙ k => (f ∙ g) ∙ s2
    assoc H K =
      transport (λ i → (to-path H i ∙ h ∙ k) => ((f ∙ g) ∙ to-path K i)) hrefl

record abstract-virtual-graph u v w z : Type₊ (u ⊔ v ⊔ w ⊔ z) where
  field
    ob : Type u
    hom : ob → Type v
    hom-op : ob → Type w
    disp-hom : ∀ x → hom-op x → Type z
    concat : ∀ {x} (b : hom-op x) → hom x → disp-hom x b

module composite-system {u v w z e} {A : Type u}
  (B : A → Type v)
  (C : A → Type w)
  (D : ∀ x → B x → Type z)
  (concat : ∀ {x} (b : B x) → C x → D x b)
  (E : ∀ {x} {b : B x} → D x b → D x b → Type e)
  (comp-prop : ∀ {x} {f : B x} {g : C x} → is-prop (Σ s ∶ D x f , E (concat f g) s))
  (crefl : ∀ {x} {f : B x} {g : C x} → E (concat f g) (concat f g))
  where
    private
      _=>_ = E; infix 4 _=>_
      _∙_ = concat
      --_⨾_ = hconcat
      infixr 40 _∙_ -- _⨾_

    ccenter : ∀ {x} {f : B x} {g : C x} → Σ s ∶ D x f , f ∙ g => s
    ccenter {f} {g} = f ∙ g , crefl

    contractible : ∀ {x} {f : B x} {g : C x}
                 → is-contr (Σ s ∶ D x f , f ∙ g => s)
    contractible .center = ccenter
    contractible .paths p = comp-prop ccenter p

    prop : ∀ {x} {f : B x} {g : C x} → is-prop (Σ s ∶ D x f , f ∙ g => s)
    prop {f} {g} = is-contr→is-prop (contractible)

    to-path : ∀ {x} {f : B x} {g : C x} {s : D x f}
            → f ∙ g => s → f ∙ g ＝ s
    to-path {f} {g} {s} h = ap fst (contractible .paths (s , h))

    to-pathp : ∀ {x} {f : B x} {g : C x} {s : D x f}
             → (p : f ∙ g => s) → PathP (λ i → (f ∙ g) => to-path p i) crefl p
    to-pathp {f} {g} {s} p i = {!!}

    based-ids : ∀ {x} {f : B x} {g : C x} → is-based-identity-system (f ∙ g) (f ∙ g =>_) crefl
    based-ids {f} {g} .is-based-identity-system.to-path p = to-path p
    based-ids .is-based-identity-system.to-path-over p = to-pathp p

module strict-composite-system {u v w z} {A : Type u}
  (B : A → Type v)
  (C : A → Type w)
  (D : ∀ x → B x → Type z)
  (_⨾_ : ∀ {x} (b : B x) → C x → D x b)
  --(_⨾⁻¹_ : ∀ {x} (b : C x) → B x → D x b)
  where
    crefl : ∀ {x} {f : B x} {g : C x} → (f ⨾ g) ＝ (f ⨾ g)
    crefl = refl

    ccenter : ∀ {x} {f : B x} {g : C x} → Σ s ∶ D x f , f ⨾ g ＝ s
    ccenter {f} {g} = f ⨾ g , crefl

    based-ids : ∀ {x} {f : B x} {g : C x} → is-based-identity-system (f ⨾ g) (f ⨾ g ＝_) refl
    based-ids .is-based-identity-system.to-path = λ x → x
    based-ids .is-based-identity-system.to-path-over p = λ i j → p (i ∧ j)

    contractible : ∀ {x} (f : B x) (g : C x)
                 → is-contr (Σ s ∶ D x f , f ⨾ g ＝ s)
    contractible H K .center = ccenter
    contractible H K .paths p = λ i → (p .snd i) , λ j → p .snd (i ∧ j)

    hconcat-unique : ∀ {x} {e1 d1 : B x} {e2 d2 : C x}
                   → (H : e1 ＝ d1) → e2 ＝ d2
                   → PathP (λ i → D x (H i)) (e1 ⨾ e2) (d1 ⨾ d2)
    hconcat-unique H K = λ i → H i ⨾ K i

    prop : ∀ {x} (f : B x) (g : C x) → is-prop (Σ s ∶ D x f , f ⨾ g ＝ s)
    prop f g = is-contr→is-prop (contractible f g)

    module naturality {x y} (p : x ＝ y) (f : B x) (g : C x) where
      -- Transport the factors
      f' : B y
      f' = subst B p f

      g' : C y
      g' = subst C p g

      -- Two ways to get a composite in D y f':

      -- -- Way 1: compose then transport
      -- way1 : D y f'
      -- way1 = transport (λ i → D (p i) (transport-filler (λ _ → {!!}) p {!!} i)) (f ⨾ g)

      -- Way 2: transport then compose
      way2 : D y f'
      way2 = f' ⨾ g'

      -- -- By contractibility, these should be related
      -- naturality-square : way1 ＝ way2
      -- naturality-square = ap fst (is-contr→is-prop (contractible f' g') (way1 , {!!}) (way2 , {!!}))




module strict-composites {u v} (G : Graph u v)
  (let module G = Graph G)
  (_⨾_ : {x y z : G.₀} → G.₁ x y → G.₁ y z → G.₁ x z)
  where
    open Graph G renaming (₀ to ob; ₁ to _~>_)
    crefl : ∀ {x y z} {f : G.₁ x y} {g : G.₁ y z} → f ⨾ g ＝ f ⨾ g
    crefl = refl

    ccenter : ∀ {x y z} {f : G.₁ x y} {g : G.₁ y z} → Σ s ∶ x ~> z , f ⨾ g ＝ s
    ccenter {f} {g} = f ⨾ g , crefl

    contractible : ∀ {x y z} (f : x ~> y) (g : y ~> z)
                 → is-contr (Σ s ∶ x ~> z , f ⨾ g ＝ s)
    contractible H K .center = ccenter
    contractible H K .paths p = λ i → (p .snd i) , λ j → p .snd (i ∧ j)

    hconcat-unique : ∀ {x y z} {e1 d1 : x ~> y} {e2 d2 : y ~> z}
                   → e1 ＝ d1 → e2 ＝ d2
                   → (e1 ⨾ e2) ＝ (d1 ⨾ d2)
    hconcat-unique H K = λ i → H i ⨾ K i

    prop : ∀ {x y z} (f : x ~> y) (g : y ~> z)
                   → is-prop (Σ s ∶ x ~> z , f ⨾ g ＝ s)
    prop H K = is-contr→is-prop (contractible H K)

    cofibroid : ∀ {x y z} → x ~> y → x ~> z → Type v
    cofibroid {y = y} {z} f s = Σ h ∶ (y ~> z) , f ⨾ h ＝ s

    fibroid : ∀ {a x y} → x ~> y → a ~> y → Type v
    fibroid {a} {x} f s = Σ h ∶ a ~> x , h ⨾ f ＝ s

    has-path : ∀ {x y z} → x ~> y → y ~> z → Type v
    has-path {x} {z} f g = Σ h ∶ x ~> z , f ⨾ g ＝ h

    is-left-cocartesian : ∀ {x y z} (p : x ~> y) (q : x ~> z) → Type v
    is-left-cocartesian p q = is-contr (cofibroid p q)

    is-right-cocartesian : ∀ {a x y} (p : x ~> y) (q : a ~> y) → Type v
    is-right-cocartesian p q = is-contr (fibroid p q)

    record is-cocartesian {x y} (q : x ~> y) : Type (u ⊔ v) where
      field
        left : (∀ {z} (s : x ~> z) → is-left-cocartesian q s)
        right :(∀ {w} (s : w ~> y) → is-right-cocartesian q s)
