```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Graph.Virtual where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Core.Kan
open import Lib.Path hiding (to-path; to-path-over)
open import Lib.Equal hiding (_∙_; _⨾_)
open import Lib.Graph
open import Lib.Underlying

module [1] where
  data _≤_ : Bool → Bool → Type where
    Lt : ff ≤ tt
    Min : ff ≤ ff
    Max : tt ≤ tt

  not-tt-to-ff : ¬ (tt ≤ ff)
  not-tt-to-ff ()

  -- there are no composites
  concat : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  concat Lt Max = Lt
  concat Min g = g
  concat Max g = g

  assoc : ∀ {w x y z} (f : w ≤ x) (g : x ≤ y) (h : y ≤ z)
        → concat (concat f g) h ＝ concat f (concat g h)
  assoc Lt Max h = refl
  assoc Min g h = refl
  assoc Max g h = refl

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
    --vconcat : ∀ {x y} {f g h : x ~> y} → f => g → g => h → f => h

V-graph : (u v w : Level) → Type₊ (u ⊔ v ⊔ w)
V-graph u v w = Σ G ∶ Graph u v , is-virtual-graph w G

module V-graph {u v w} ((G , V) : V-graph u v w) where
  open Graph G renaming (₀ to Ob; ₁ to infix 4 _~>_)
  private
    module V = is-virtual-graph V
    _∙_ = V.concat
    _=>_ = V.₂
    infixr 40 _∙_ -- _⨾_
  ₀ = Ob
  ₁ = _~>_
  ₂ = _=>_

  concat = V.concat
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
  loop {s} p = subst (_=> s) (to-path p) p

  lift-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {r s : x ~> z}
            → f ∙ g => r → r ＝ s →  r => s
  lift-path {r} {s} K p = subst (r =>_) p (loop K)

  module composite-coherence {x y z : Ob} {f : x ~> y} {g : y ~> z} where
    2-prop : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
          → (α : f ∙ g => s) (β : f ∙ g => s')
          → (s , α) ＝ (s' , β)
    2-prop α β = composites-prop (_ , α) (_ , β)
    2-fibers : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
            → (α : f ∙ g => s)
            → hcenter ＝ (s , α)
    2-fibers {f} {g} {s} α = composites-prop (_ , hrefl) (_ , α)
    private
      C : Type _
      C = Σ s ∶ (x ~> z) , f ∙ g => s

    -- The strict contraction: computes to refl at hcenter when to-path/to-pathp do
    contraction : (p : C) → hcenter ≡ p
    contraction (s , α) i = to-path α i , to-pathp α i

    -- This IS composites-contr, but structured for computation:
    cc : is-contr C
    cc .center = hcenter
    cc .paths = contraction

    -- C is a set (all paths are equal)
    C-is-set : is-set C
    C-is-set = is-contr→is-set cc

    -- Therefore: any two squares with the same boundary are equal
    -- This subsumes 3-coherence and all higher
    square-unique : {p q r s : C} {top : p ≡ q} {bot : r ≡ s} {left : p ≡ r} {right : q ≡ s}
                  → (sq1 sq2 : Square bot left top right)
                  → sq1 ≡ sq2
    square-unique sq1 sq2 = is-prop→SquareP (λ _ _ → C-is-set _ _) sq1 sq2 _ _

    -- Your 3-coherence is an instance:
    3-coherence' : {s s' : x ~> z} (α : f ∙ g => s) (β : f ∙ g => s')
                 → (sq1 sq2 : Square (2-fibers α) (2-fibers β) refl (2-prop α β))
                 → sq1 ≡ sq2
    3-coherence' α β = square-unique

    -- -- In particular, 2-coherence α β ≡ 2-idem α β
    -- 2-coherence-unique : {s s' : x ~> z} (α : f ∙ g => s) (β : f ∙ g => s')
    --                    → 2-coherence α β ≡ 2-idem α β
    -- 2-coherence-unique α β = square-unique _ _

    -- The fundamental coherence: contraction paths form a cone over prop-paths
    -- This replaces 2-idem with a cleaner construction
    -- contraction-square : (p q : C) → Square (contraction p) (contraction q) refl (composites-prop p q)
    -- contraction-square p q i j = contraction (composites-prop p q i) j

    -- Unfolding for your 2-cell notation:
    -- 2-coherence : {s s' : x ~> z} (α : f ∙ g => s) (β : f ∙ g => s')
    --             → Square (2-fibers α) (2-fibers β) refl (2-prop α β)
    -- 2-coherence α β i j = contraction (2-prop α β i) j

    -- The j=i0 face: refl (since contraction of anything at j=0 is hcenter)
    -- The j=i1 face: 2-prop α β (the path between (s,α) and (s',β))
    -- The i=i0 face: 2-fibers α (contraction to (s,α))
    -- The i=i1 face: 2-fibers β (contraction to (s',β))

  module encode-decode {x y z} {f : x ~> y} {g : y ~> z} where
    encode : ∀ {s} → f ∙ g ≡ s → f ∙ g => s
    encode p = subst (f ∙ g =>_) p hrefl

    decode : ∀ {s} → f ∙ g => s → f ∙ g ≡ s
    decode = to-path

    -- The key fillers for the equivalence
    encode-filler : ∀ {s} (p : f ∙ g ≡ s)
                  → PathP (λ i → f ∙ g => p i) hrefl (encode p)
    encode-filler p = transport-filler (λ i → f ∙ g => p i) hrefl

    -- encode-decode : ∀ {s} (α : f ∙ g => s) → encode (decode α) ≡ α
    -- encode-decode α i = to-pathp α i  -- this IS the content of to-pathp

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

  module apl-coherence {w x y z : Ob} {f : x ~> y} {g : y ~> z} {s : x ~> z}
    (h : w ~> x) (α β : f ∙ g => s) where
    -- apl h α : h ∙ (f ∙ g) => h ∙ s
    -- apl h β : h ∙ (f ∙ g) => h ∙ s
    -- Both target h ∙ s!

    -- By the same-target lemma applied to the composite h ∙ (f ∙ g):
    apl-fiber-path : (h ∙ s , apl h α) ≡ (h ∙ s , apl h β)
    apl-fiber-path = composites-prop (h ∙ s , apl h α) (h ∙ s , apl h β)

    -- The base component:
    apl-base-loop : h ∙ s ≡ h ∙ s
    apl-base-loop = ap fst apl-fiber-path

    -- If homs are sets, this is refl, and we get:
    hom-set→apl-cells-equal : (hom-set : is-set (w ~> z)) → apl h α ≡ apl h β
    hom-set→apl-cells-equal hom-set =
      subst (λ p → PathP (λ i → h ∙ (f ∙ g) => p i) (apl h α) (apl h β))
            (hom-set _ _ apl-base-loop refl)
            (ap snd apl-fiber-path)

    -- We always have a path in the Σ type:
    apl-2-prop : (h ∙ s , apl h α) ≡ (h ∙ s , apl h β)
    apl-2-prop = composites-prop _ _

    -- This gives us a Square relating the transport fillers:
    --
    --              refl
    --    h ∙ (f ∙ g) ═══════ h ∙ (f ∙ g)
    --         ║                   ║
    --  apl-filler h α        apl-filler h β
    --         ║                   ║
    --         ▼                   ▼
    --       h ∙ s ─────────── h ∙ s
    --            apl-base-loop
    --
    -- The top is refl (both start at h ∙ (f ∙ g))
    -- The sides are the transport fillers
    -- The bottom might be a nontrivial loop

    -- But crucially: any two paths h ∙ s ≡ h ∙ s through apl are equal
    -- because they all factor through the contractible Σ type!




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

Cocartesian morphisms and isomorphism

```

  is-left-cocartesian : {x y z : Ob} (p : x ~> y) (q : x ~> z) → Type (v ⊔ w)
  is-left-cocartesian p q = is-contr (cofibroid p q)

  is-right-cocartesian : {a x y : Ob} (p : x ~> y) (q : a ~> y) → Type (v ⊔ w)
  is-right-cocartesian p q = is-contr (fibroid p q)

  record is-cocartesian {x y : Ob} (q : x ~> y) : Type (u ⊔ v ⊔ w) where
    field
      left : (∀ {z : Ob} (s : x ~> z) → is-contr (cofibroid q s))
      right :(∀ {w : Ob} (s : w ~> y) → is-contr (fibroid q s))

  _≅_ : Ob → Ob → Type (u ⊔ v ⊔ w)
  x ≅ y = Σ f ∶ x ~> y , is-cocartesian f
  infix 4 _≅_

  is-cocartesian-is-prop : {x y : Ob} (q : x ~> y) → is-prop (is-cocartesian q)
  is-cocartesian-is-prop q x y i .is-cocartesian.left s = is-contr-is-prop (cofibroid q s) (x .is-cocartesian.left s) (y .is-cocartesian.left s) i
  is-cocartesian-is-prop q x y i .is-cocartesian.right s = is-contr-is-prop (fibroid q s) (x .is-cocartesian.right s) (y .is-cocartesian.right s) i

  2-prop : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
          → (α : f ∙ g => s) (β : f ∙ g => s')
          → (s , α) ＝ (s' , β)
  2-prop α β = composites-prop (_ , α) (_ , β)

  lower-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
           → f ∙ g => s → f ∙ g => s' → s ＝ s'
  lower-path α β = ap fst (2-prop α β)

  2-fibers : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
            → (α : f ∙ g => s)
            → hcenter ＝ (s , α)
  2-fibers {f} {g} {s} α = 2-prop hrefl α

  2-op-fibers : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
            → (α : f ∙ g => s)
            → (s , α) ＝ hcenter
  2-op-fibers {f} {g} {s} α = 2-prop α hrefl

  2-idem : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s s' : x ~> z}
         → (α : f ∙ g => s) (β : f ∙ g => s')
         → PathP (λ i → 2-fibers α (~ i) ≡ 2-fibers β (~ i)) (2-prop α β)
                 (cat (erefl hcenter) (erefl hcenter))
  2-idem {f} {g} {s} {s'} α β j i = hfill (∂ i) j λ where
      k (i = i0) → p (~ j)
      k (i = i1) → q (~ j)
      k (k = i0) → 2-prop hrefl (path i .snd) (~ j) .fst , 2-prop hrefl (path i .snd) (~ j) .snd
    where
    cc = composites-contr f g
    c = cc .center

    p = 2-fibers α
    q = 2-fibers β

    path : (s , α) ＝ (s' , β)
    path = composites-prop (s , α) (s' , β)

  3-op-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
            → (α : f ∙ g => s)
            → 2-prop α hrefl ＝ cat (erefl (s , α)) (2-op-fibers α)
  3-op-path {f} {g} α =  is-contr→is-set (composites-contr f g) _ _ (2-prop α hrefl) (cat refl (2-op-fibers α))

  3-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
         → (α : f ∙ g => s)
         → 2-prop hrefl α ＝ cat (2-fibers α) (erefl (s , α))
  3-path {f} {g} α = is-contr→is-set (composites-contr f g) _ _ (2-prop hrefl α) (cat (2-fibers α) refl)

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
    unit-prop s = is-contr→is-prop (unit-equiv s)

    divr : ∀ {z} → x ~> z → y ~> z
    divr s = counit.center s .fst

    rhtpy : ∀ {z} → (s : x ~> z) →  q ∙ divr s => s
    rhtpy s = counit.center s .snd

    rpaths : ∀ {z} → (s : x ~> z) ((e , u) : cofibroid q s) → (divr s , rhtpy s) ＝ (e , u)
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

    lsym-unique : (h : y ~> x) → q ∙ h => q ∙ lsym → lsym ＝ h
    lsym-unique h α = ap fst (counit-prop (q ∙ lsym) (lsym , hrefl) (h , α))

    lsym-contr : is-contr (Σ r ∶ y ~> x , q ∙ r  => (q ∙ lsym))
    lsym-contr .center = lsym , hrefl
    lsym-contr .paths (r , ε) i = (lsym-unique r ε i) , counit-prop (q ∙ lsym) (lsym , V.hrefl) (r , ε) i .snd

    rsym-contr : is-contr (Σ s ∶ y ~> x , s ∙ q  => divr (divl q) ∙ q)
    rsym-contr .center = divr (divl q) , hrefl
    rsym-contr .paths (r , ε) i = unit-prop (divr unit ∙ q) (divr unit , V.hrefl) (r , ε) i

    rsym : y ~> x
    rsym = rsym-contr .center .fst

    J-lsym : ∀ {ℓ} (P : (r : y ~> x) → q ∙ r => q ∙ lsym → Type ℓ)
           → P lsym hrefl
           → ∀ r ε → P r ε
    J-lsym P base r ε = subst (λ (r , ε) → P r ε) (lsym-contr .paths (r , ε)) base

    J-rsym : ∀ {ℓ} (P : (s : y ~> x) → s ∙ q => rsym ∙ q → Type ℓ)
           → P rsym hrefl
           → ∀ s ε → P s ε
    J-rsym P base s ε = subst (λ (s , ε) → P s ε) (rsym-contr .paths (s , ε)) base

    -- to-path for unit
    unit-to-path : (h : x ~> x) → h ∙ q => q → unit ＝ h
    unit-to-path h α = ap fst (lpaths q (h , α))

    -- to-path for counit
    counit-to-path : (h : y ~> y) → q ∙ h => q → counit ＝ h
    counit-to-path h α = ap fst (rpaths q (h , α))

    -- to-path for lsym
    lsym-to-path : (r : y ~> x) → q ∙ r => q ∙ lsym → lsym ＝ r
    lsym-to-path r ε = ap fst (lsym-contr .paths (r , ε))

    -- to-path for rsym
    rsym-to-path : (s : y ~> x) → s ∙ q => rsym ∙ q → rsym ＝ s
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

    invl-to-path : (h : y ~> x) → h ∙ q => counit → lsym ＝ h
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

    invr-to-path : (h : y ~> x) → q ∙ h => unit → rsym ＝ h
    invr-to-path h α = ap fst (counit-prop unit (rsym , invr) (h , α))

    -- fibroid q (rsym ∙ q) = Σ h : y ~> x, h ∙ q => rsym ∙ q
    -- Center: (rsym, hrefl)

    -- J-rsym : (P : (h : y ~> y) → rsym ∙ q => h → Type)
    --          → P rsym invr
    --          → ∀ h α → P h α
    -- J-rsym P base h α = subst (λ (h , α) → P h α) (unit-prop (rsym ∙ q) (h , α) {!!}) {!!}

    midpoint : unit ∙ q => q ∙ counit
    midpoint = lift-path hrefl (cat (to-path unitp) (sym (to-path counitp)))

  module lin-thk-props {x y : Ob} (idn : x ~> x) (cc : is-cocartesian idn) where
    private module iso = cocartesian idn cc

    lin-is-prop : (f : x ~> y) → is-prop (idn ∙ (idn ∙ f) => idn ∙ f)
    lin-is-prop f lin₁ lin₂ = goal where
      C = iso.counit-equiv (idn ∙ f)
      c = C .center
      d = c .fst
      r = c .snd  -- r : idn ∙ d => idn ∙ f

      to₁ : c ≡ (idn ∙ f , lin₁)
      to₁ = C .paths _

      to₂ : c ≡ (idn ∙ f , lin₂)
      to₂ = C .paths _

      -- Paths in the hom type from center to idn ∙ f
      p₁ : d ≡ idn ∙ f
      p₁ = ap fst to₁

      p₂ : d ≡ idn ∙ f
      p₂ = ap fst to₂

      -- Dependent paths from r to lin₁ and lin₂
      r-to-lin₁ : PathP (λ i → idn ∙ p₁ i => idn ∙ f) r lin₁
      r-to-lin₁ = ap snd to₁

      r-to-lin₂ : PathP (λ i → idn ∙ p₂ i => idn ∙ f) r lin₂
      r-to-lin₂ = ap snd to₂

      -- Square in the hom type with corners at d
      hom-sq : I → I → x ~> y
      hom-sq i j = hfill (∂ i) j λ where
        k (i = i0) → p₁ k
        k (i = i1) → p₂ k
        k (k = i0) → d

      -- At j=1, hom-sq i i1 = idn ∙ f at both i=0 and i=1
      -- (since p₁ i1 = p₂ i1 = idn ∙ f)

      goal : lin₁ ≡ lin₂
      goal i = {!!}

    thk-is-prop : {w : Ob} (f : w ~> x) → is-prop ((f ∙ idn) ∙ idn => f ∙ idn)
    thk-is-prop {w} f thk₁ thk₂ = goal where
      C = iso.unit-equiv (f ∙ idn)
      c = C .center
      d = c .fst
      r = c .snd  -- r : d ∙ idn => f ∙ idn

      to₁ : c ≡ (f ∙ idn , thk₁)
      to₁ = C .paths _

      to₂ : c ≡ (f ∙ idn , thk₂)
      to₂ = C .paths _

      p₁ : d ≡ f ∙ idn
      p₁ = ap fst to₁

      p₂ : d ≡ f ∙ idn
      p₂ = ap fst to₂

      r-to-thk₁ : PathP (λ i → p₁ i ∙ idn => f ∙ idn) r thk₁
      r-to-thk₁ = ap snd to₁

      r-to-thk₂ : PathP (λ i → p₂ i ∙ idn => f ∙ idn) r thk₂
      r-to-thk₂ = ap snd to₂

      hom-sq : I → I → w ~> x
      hom-sq i j = hfill (∂ i) j λ where
        k (i = i0) → p₁ k
        k (i = i1) → p₂ k
        k (k = i0) → d

      goal : thk₁ ≡ thk₂
      goal i = {!!}
      -- comp (λ j → hom-sq i j ∙ idn => f ∙ idn) (∂ i) λ where
      --  j (i = i0) → r-to-thk₁ j
      --  j (i = i1) → r-to-thk₂ j
      --  j (j = i0) → ?

  cocart-idem-unique : ∀ {x} (q q' : x ~> x)
                     → (cq : is-cocartesian q) (cq' : is-cocartesian q')
                     → (idem-q : q ∙ q => q)
                     → (let k = cq' .is-cocartesian.left q .center .fst
                            H = cq' .is-cocartesian.left q .center .snd)
                     → q' ∙ (q' ∙ k) => (q' ∙ k)
                     → q ＝ q'
  cocart-idem-unique {x} q q' cq cq' idem-q lin = ap fst path where
    module iso = cocartesian q cq
    module iso' = cocartesian q' cq'

    k = iso'.divr q
    q'k=>q = iso'.rhtpy q

    -- The two key coherences from contractibility
    lin-coh : (q' ∙ k , lin) ≡ (k , hrefl)
    lin-coh = iso'.counit-prop (q' ∙ k) _ _

    the-path : PathP (λ i → q' ∙ lin-coh i .fst => (q' ∙ k)) lin hrefl
    the-path = ap snd lin-coh

    comp-coh : (q' ∙ k , hrefl) ≡ (q , q'k=>q)
    comp-coh = 2-prop hrefl q'k=>q

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

  cocart-idem-unique-alt : ∀ {x} (q q' : x ~> x)
                     → (cq : is-cocartesian q) (cq' : is-cocartesian q')
                     → (idem-q : q ∙ q => q)
                     → (let k = cq' .is-cocartesian.left q .center .fst)
                     → (lin : q' ∙ (q' ∙ k) => (q' ∙ k))
                     → (q , idem-q) ＝ (q' , {!!})
  cocart-idem-unique-alt {x} q q' cq cq' idem-q lin =
    is-contr→is-prop (cq .is-cocartesian.right q) (q , idem-q) (q' , q'q=>q)
      where
        -- module cq = is-cocartesian cq
        -- module cq' = is-cocartesian cq'

        module cc = cocartesian q cq
        module cc' = cocartesian q' cq'

        -- Step 1: get k with q' ∙ k => q
        k0 : x ~> x
        k0 = cc'.divl q
        k1 : x ~> x
        k1 = cc'.divr q

        q'k=>q : q' ∙ k1 => q
        q'k=>q = cc'.rhtpy q

        q'q=>q : q' ∙ q => q
        q'q=>q = weak-vconcat (overlap-coh.rwhisk-op q'k=>q) (weak-vconcat lin q'k=>q)

        counitp' : (q' ∙ cc'.counit) => q'
        counitp' = cc'.counitp

        unitp' : (cc'.unit ∙ q') => q'
        unitp' = cc'.unitp

        f0 : q' ∙ q ＝ q
        f0 i = composites-prop (q' ∙ q , hrefl) (q , q'q=>q) i .fst

  cocart-idem-unique' : ∀ {x} (q q' : x ~> x)
                      → (cq : is-cocartesian q) (cq' : is-cocartesian q')
                      → (idem-q : q ∙ q => q)
                      → (let k' = cq' .is-cocartesian.right q .center .fst)
                      → (thk : (k' ∙ q') ∙ q' => k' ∙ q')
                      → q ≡ q'
  cocart-idem-unique' {x} q q' cq cq' idem-q thk = ap fst path where
    module iso = cocartesian q cq
    module iso' = cocartesian q' cq'

    k' = iso'.divl q
    k'q'=>q = iso'.lhtpy q

    -- The two key coherences from contractibility
    thk-coh : (k' ∙ q' , thk) ≡ (k' , hrefl)
    thk-coh = iso'.unit-prop (k' ∙ q') _ _

    comp-coh : (k' ∙ q' , hrefl) ≡ (q , k'q'=>q)
    comp-coh = 2-prop hrefl k'q'=>q

    -- k' acts as right identity absorbed by q' (from thk-coh)
    -- and k' ∙ q' = q (from k'q'=>q)
    -- So k' = k' ∙ q' = q

    k'≡k'q' : k' ≡ k' ∙ q'
    k'≡k'q' = sym (ap fst thk-coh)

    k'q'≡q : k' ∙ q' ≡ q
    k'q'≡q = to-path k'q'=>q

    k'≡q : k' ≡ q
    k'≡q = cat k'≡k'q' k'q'≡q

    -- Now transport k'q'=>q along k'≡q
    qq'=>q : q ∙ q' => q
    qq'=>q = transport (λ i → k'≡q i ∙ q' => q) k'q'=>q

    path : (q , idem-q) ≡ (q' , qq'=>q)
    path = iso.counit-prop q _ _

  -- cocart-idem-unique' : ∀ {x} (q q' : x ~> x)
  --                     → (cq : is-cocartesian q) (cq' : is-cocartesian q')
  --                     → (idem-q : q ∙ q => q)
  --                     → (let k' = cq' .is-cocartesian.right q .center .fst)
  --                     → ((k' ∙ q') ∙ q') => (k' ∙ q')
  --                     → q ＝ q'
  -- cocart-idem-unique' {x} q q' cq cq' idem-q thk =
  --     ap fst (is-contr→is-prop (cq .is-cocartesian.left q) (q , idem-q) (q' , qq'=>q))
  --     where
  --       module cq = is-cocartesian cq
  --       module cq' = is-cocartesian cq'

  --       -- Step 1: get k' with k' ∙ q' => q
  --       k' : x ~> x
  --       k' = cq'.right q .center .fst

  --       k'q'=>q : k' ∙ q' => q
  --       k'q'=>q = cq'.right q .center .snd

  --       -- Chain: q ∙ q' => (k' ∙ q') ∙ q' => k' ∙ q' => q
  --       qq'=>q : q ∙ q' => q
  --       qq'=>q = weak-vconcat (overlap-coh.lwhisk-op k'q'=>q) (weak-vconcat thk k'q'=>q)

  record has-unit x : Type (u ⊔ v ⊔ w) where
    field
      idn : x ~> x
      iso : is-cocartesian idn
      lin : ∀ {y} (f : x ~> y) → idn ∙ (idn ∙ f) => idn ∙ f

  module has-unit-lemmas {x : Ob} (hu : has-unit x) where
    private module hu = has-unit hu
    private module iso = cocartesian hu.idn hu.iso

    idn : x ~> x
    idn = hu.idn

    -- The key coherence: (idn ∙ f, lin f) and (f, hrefl) are both in cofibroid idn (idn ∙ f)
    lin-coh : ∀ {y} (f : x ~> y) → (idn ∙ f , hu.lin f) ≡ (f , hrefl)
    lin-coh f = iso.counit-prop (idn ∙ f) _ _

    unitl-comp : ∀ {y} (f : x ~> y) → idn ∙ f ≡ f
    unitl-comp f = ap fst (lin-coh f)

    -- The PathP from lin-coh directly gives the 2-cell structure
    unitl-pathp : ∀ {y} (f : x ~> y) → PathP (λ i → idn ∙ unitl-comp f i => idn ∙ f) (hu.lin f) hrefl
    unitl-pathp f = ap snd (lin-coh f)

    unitl : ∀ {y} (f : x ~> y) → idn ∙ f => f
    unitl f = subst (idn ∙ f =>_) (unitl-comp f) hrefl

    idem : idn ∙ idn => idn
    idem = unitl idn

    -- To show idn = iso.counit, use that both (idn, counitp) and (iso.counit, unitl iso.counit)
    -- live in the contractible Σ s, idn ∙ iso.counit => s
    counit-coh : (idn , iso.counitp) ≡ (iso.counit , unitl iso.counit)
    counit-coh = composites-prop _ _

    idn-is-counit : idn ≡ iso.counit
    idn-is-counit = ap fst counit-coh

    -- counit-path via the PathP from counit-coh
    counit-pathp : PathP (λ i → idn ∙ iso.counit => idn-is-counit i) iso.counitp (unitl iso.counit)
    counit-pathp = ap snd counit-coh

    -- For lsym-idn, we need idn in fibroid idn iso.counit = Σ h, h ∙ idn => iso.counit
    -- We have idem : idn ∙ idn => idn, and idn-is-counit : idn = iso.counit
    -- So we need: idn ∙ idn => iso.counit
    idn-counit : fibroid idn iso.counit
    idn-counit = idn , transport (λ i → (idn ∙ idn) => unitl-comp (idn-is-counit i) i) hrefl

    lsym-idn : iso.lsym ≡ idn
    lsym-idn = ap fst (iso.lpaths iso.counit idn-counit)

  record has-counit x : Type (u ⊔ v ⊔ w) where
    field
      idn : x ~> x
      iso : is-cocartesian idn
      thk : ∀ {w} (f : w ~> x) → (f ∙ idn) ∙ idn => f ∙ idn

  module has-counit-lemmas {x : Ob} (co : has-counit x) where
    private module co = has-counit co
    private module iso = cocartesian co.idn co.iso

    idn : x ~> x
    idn = co.idn

    -- Dual coherence from cocartesian structure
    thk-coh : ∀ {w} (f : w ~> x) → (f ∙ idn , co.thk f) ≡ (f , hrefl)
    thk-coh f = iso.unit-prop (f ∙ idn) _ _

    unitr-comp : ∀ {w} (f : w ~> x) → f ∙ idn ≡ f
    unitr-comp f = ap fst (thk-coh f)

    unitr-pathp : ∀ {w} (f : w ~> x) → PathP (λ i → unitr-comp f i ∙ idn => f ∙ idn) (co.thk f) hrefl
    unitr-pathp f = ap snd (thk-coh f)

    unitr : ∀ {w} (f : w ~> x) → f ∙ idn => f
    unitr f = transport (λ i → (f ∙ co.idn) => unitr-comp f i) hrefl

    idem : idn ∙ idn => idn
    idem = unitr idn

    -- Dual: show idn = iso.unit
    unit-coh : (idn , iso.unitp) ≡ (iso.unit , unitr iso.unit)
    unit-coh = composites-prop _ _

    idn-is-unit : idn ≡ iso.unit
    idn-is-unit = ap fst unit-coh

    unit-pathp : PathP (λ i → (iso.unit ∙ co.idn) => idn-is-unit i) iso.unitp (unitr iso.unit)
    unit-pathp = ap snd unit-coh

    -- For rsym-idn, we need idn in cofibroid idn iso.unit = Σ h, idn ∙ h => iso.unit
    idn-unit : cofibroid idn iso.unit
    idn-unit = idn , transport (λ i → (idn ∙ idn) => unitr-comp (idn-is-unit i) i) hrefl

    rsym-idn : iso.rsym ≡ idn
    rsym-idn = ap fst (iso.rpaths iso.unit idn-unit)

  has-unit-is-prop : ∀ {x} → is-prop (has-unit x)
  has-unit-is-prop {x} u u' = path where
    module u = has-unit u
    module u' = has-unit u'
    module iso = cocartesian u.idn u.iso
    module iso' = cocartesian u'.idn u'.iso
    module ul = has-unit-lemmas u
    module ul' = has-unit-lemmas u'

    -- Get idn-path from cocart-idem-unique
    k : x ~> x
    k = iso'.counit-equiv u.idn .center .fst

    idn-path : u.idn ≡ u'.idn
    idn-path = cocart-idem-unique u.idn u'.idn u.iso u'.iso ul.idem (u'.lin k)

    iso-path : PathP (λ i → is-cocartesian (idn-path i)) u.iso u'.iso
    iso-path = is-prop→PathP (λ i → is-cocartesian-is-prop (idn-path i)) u.iso u'.iso

    -- For lin-path, use (f, hrefl) as the common element
    lin-path : PathP (λ i → ∀ {y} (f : x ~> y) → idn-path i ∙ (idn-path i ∙ f) => idn-path i ∙ f) u.lin u'.lin
    lin-path i {y} f = {!!}
      where
        -- Contraction paths from the two cocartesian structures
        lin-coh0 : (u.idn ∙ f , u.lin f) ≡ (f , hrefl)
        lin-coh0 = iso.counit-prop (u.idn ∙ f) _ _

        lin-coh1 : (u'.idn ∙ f , u'.lin f) ≡ (f , hrefl)
        lin-coh1 = iso'.counit-prop (u'.idn ∙ f) _ _


    path : u ≡ u'
    path i = record { idn = idn-path i ; iso = iso-path i ; lin = lin-path i }

  is-cocartesian→is-linear-is-prop : ∀ {x y} (idn : x ~> x) (cc : is-cocartesian idn)
                                   → (f : x ~> y) → is-prop (idn ∙ idn ∙ f => idn ∙ f)
  is-cocartesian→is-linear-is-prop {x} {y} idn cc f α β = goal where
    module iso = cocartesian idn cc

    C : is-contr (cofibroid idn (idn ∙ f))
    C = iso.counit-equiv (idn ∙ f)

    -- The total space is a set (contractible → prop → set)
    C-is-set : is-set (cofibroid idn (idn ∙ f))
    C-is-set = is-contr→is-set C

    -- Path in the total space from contractibility
    total-path : (idn ∙ f , α) ≡ (idn ∙ f , β)
    total-path = is-contr→is-prop C _ _

    -- First component is a loop at idn ∙ f
    fst-loop : idn ∙ f ≡ idn ∙ f
    fst-loop = ap fst total-path

    -- In a set, all loops equal refl
    fst-loop-is-refl : fst-loop ≡ refl
    fst-loop-is-refl = {!!}

    -- The second component gives a PathP over fst-loop
    snd-pathp : PathP (λ i → idn ∙ fst-loop i => idn ∙ f) α β
    snd-pathp i = total-path i .snd

    -- Transport along fst-loop-is-refl to get a path over refl, i.e., α ≡ β
    goal : α ≡ β
    goal = subst (λ p → PathP (λ i → idn ∙ p i => idn ∙ f) α β) {!!} snd-pathp

  -- has-unit-is-prop : ∀ {x} → is-prop (has-unit x)
  -- has-unit-is-prop {x} u u' = path module has-unit-is-prop where
  --   private module u = has-unit u
  --   private module u' = has-unit u'
  --   private module iso = cocartesian u.idn u.iso
  --   private module iso' = cocartesian u'.idn u'.iso

  --   counit-prop = iso.counit-prop
  --   counit-prop' = iso'.counit-prop

  --   -- Derive idem from lin via the unitl-comp construction
  --   lin-coh : ∀ {y} (f : x ~> y) → (u.idn ∙ f , u.lin f) ＝ (f , hrefl)
  --   lin-coh f = counit-prop (u.idn ∙ f) _ _

  --   -- Derive idem from lin via the unitl-comp construction
  --   lin'-coh : ∀ {y} (f : x ~> y) → (u'.idn ∙ f , u'.lin f) ＝ (f , hrefl)
  --   lin'-coh f = counit-prop' (u'.idn ∙ f) _ _

  --   unitl-comp : ∀ {y} (f : x ~> y) → u.idn ∙ f ＝ f
  --   unitl-comp f = ap fst (lin-coh f)

  --   unitl-comp' : ∀ {y} (f : x ~> y) → u'.idn ∙ f ＝ f
  --   unitl-comp' f = ap fst (lin'-coh f)

  --   idem : u.idn ∙ u.idn => u.idn
  --   idem = subst (u.idn ∙ u.idn =>_) (unitl-comp u.idn) hrefl

  --   private
  --     -- k from u'.iso for cocart-idem-unique
  --     k : x ~> x
  --     k = iso'.counit-equiv u.idn .center .fst

  --   -- u'.lin k gives exactly the assoc data needed
  --   idn-path : u.idn ＝ u'.idn
  --   idn-path = cocart-idem-unique u.idn u'.idn u.iso u'.iso idem (u'.lin k)

  --   idn-path' : u.idn ＝ u'.idn
  --   idn-path' = cat (sym (unitl-comp u.idn)) (cat {!!} (unitl-comp u'.idn))

  --   _ : ∀ {y} (f : x ~> y) → {!!}
  --   _ = λ f → counit-prop (u.idn ∙ f) (u.idn ∙ f , u.lin f) (u'.idn ∙ f , weak-vconcat {!!} (u.lin f))

  --   -- iso fields match by is-cocartesian-is-prop
  --   iso-path : PathP (λ i → is-cocartesian (idn-path i)) u.iso u'.iso
  --   iso-path = is-prop→PathP (λ i → is-cocartesian-is-prop (idn-path i)) u.iso u'.iso

  --   lin-path' : PathP (λ i → ∀ {y} (f : x ~> y) → idn-path i ∙ (idn-path i ∙ f) => idn-path i ∙ f) u.lin u'.lin
  --   lin-path' i {y} f = {!!}
  --     where
  --       -- Dependent family of contractible types
  --       C : (j : I) → is-contr (cofibroid (idn-path j) (idn-path j ∙ f))
  --       C j = cocartesian.counit-equiv (idn-path j) (iso-path j) (idn-path j ∙ f)

  --       -- Contraction paths to (f, hrefl) at endpoints
  --       p0 : (u.idn ∙ f , u.lin f) ≡ (f , hrefl)
  --       p0 = iso.counit-prop (u.idn ∙ f) _ _

  --       p1 : (u'.idn ∙ f , u'.lin f) ≡ (f , hrefl)
  --       p1 = iso'.counit-prop (u'.idn ∙ f) _ _

  --       -- Fill the square using (f, hrefl) as the floor
  --       sq : I → I → cofibroid (idn-path i) (idn-path i ∙ f)
  --       sq j k = hfill (∂ j) k λ where
  --         l (j = i0) → {!!}
  --         l (j = i1) → {!!}
  --         l (l = i0) → (f , hrefl)

  --   -- lin f is propositional: it's a fiber of fst over a contractible type
  --   -- cofibroid (idn-path i) (idn-path i ∙ f) is contractible
  --   -- so fiber over (idn-path i ∙ f) is contractible when inhabited
  --   lin-path : ∀ {y} (f : x ~> y) → PathP (λ i → (idn-path i ∙ idn-path i ∙ f) => (idn-path i ∙ f)) (u.lin f) (u'.lin f) -- PathP (λ i → ∀ {y} (f : x ~> y) → idn-path i ∙ (idn-path i ∙ f) => idn-path i ∙ f) u.lin u'.lin
  --   lin-path {y} f i = {!!}
  --     where
  --     lin-coh0 : (u.idn ∙ f , u.lin f) ≡ (f , hrefl)
  --     lin-coh0 = iso.counit-prop (u.idn ∙ f) _ _

  --     lin-coh1 : (u'.idn ∙ f , u'.lin f) ≡ (f , hrefl)
  --     lin-coh1 = iso'.counit-prop (u'.idn ∙ f) _ _

  --     hrefl-path : PathP (λ i → cofibroid (idn-path i) (idn-path i ∙ f)) (f , hrefl) (f , hrefl)
  --     hrefl-path i = (f , hrefl)

  --     total-path : PathP (λ i → cofibroid (idn-path i) (idn-path i ∙ f)) (u.idn ∙ f , u.lin f) (u'.idn ∙ f , u'.lin f)
  --     total-path i = comp (λ j → cofibroid (idn-path i) (idn-path i ∙ f)) (∂ i) λ where
  --       j (i = i0) → lin-coh0 (~ j)
  --       j (i = i1) → lin-coh1 (~ j)
  --       j (j = i0) → hrefl-path i

  --   path : u ＝ u'
  --   path i .has-unit.idn = idn-path i
  --   path i .has-unit.iso = iso-path i
  --   path i .has-unit.lin f = {!!} -- lin-path i

  has-counit-is-prop : ∀ {x} → is-prop (has-counit x)
  has-counit-is-prop {x} c c' = path where
    module c = has-counit c
    module c' = has-counit c'
    module iso = cocartesian c.idn c.iso
    module iso' = cocartesian c'.idn c'.iso

    thk-coh : ∀ {w} (f : w ~> x) → (f , hrefl) ＝ (f ∙ c.idn , c.thk f)
    thk-coh f = is-contr→is-prop (iso.unit-equiv (f ∙ c.idn)) _ _

    unitr-comp : c.idn ∙ c.idn ＝ c.idn
    unitr-comp = sym (ap fst (thk-coh c.idn))

    idem : c.idn ∙ c.idn => c.idn
    idem = subst (c.idn ∙ c.idn =>_) unitr-comp (hrefl)

    k' : x ~> x
    k' = iso'.unit-equiv c.idn .center .fst

    idn-path : c.idn ＝ c'.idn
    idn-path = cocart-idem-unique' c.idn c'.idn c.iso c'.iso idem (c'.thk k')

    iso-path : PathP (λ i → is-cocartesian (idn-path i)) c.iso c'.iso
    iso-path = is-prop→PathP (λ i → is-cocartesian-is-prop (idn-path i)) c.iso c'.iso

    thk-path : PathP (λ i → ∀ {w} (f : w ~> x) → (f ∙ idn-path i) ∙ idn-path i => f ∙ idn-path i) c.thk c'.thk
    thk-path = {!!} -- is-prop→PathP (λ i → implicit-Π-is-prop λ w → Π-is-prop λ f →
      --fiber-of-contr-is-prop (cocartesian.unit-equiv (idn-path i) (iso-path i) (f ∙ idn-path i))) c.thk c'.thk

    path : c ＝ c'
    path i .has-counit.idn = idn-path i
    path i .has-counit.iso = iso-path i
    path i .has-counit.thk = thk-path i
    --record { idn = idn-path i ; iso = iso-path i ; thk = thk-path i }

  _≈_ : ∀ {x y} → (f g : x ~> y) → Type (u ⊔ v ⊔ w)
  _≈_ {x} {y} f g = Σ q ∶ x ~> y
                  , Σ M ∶ is-cocartesian q
                  , section M × retraction M × lin M × thk M
     where module _ {q : x ~> y} (cc : is-cocartesian q) where
       open cocartesian q cc

       retraction = f ∙ counit => q
       section = unit ∙ g => q
       lin = (unit ∙ unit) ∙ g => unit ∙ g
       thk = f ∙ (counit ∙ counit) => f ∙ counit


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
