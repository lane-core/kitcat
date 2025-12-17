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

-- composite structure for arbitrary virtual 2-cells
module composites {u v w} (G : Graph u v) (let module G = Graph G)
  (cut : ∀ {A B C} → G.₁ A B → G.₁ B C → G.₁ A C)
  (Htpy : ∀ {A B} → G.₁ A B → G.₁ A B → Type w)
  (heqv : ∀ {A B C} {f : G.₁ A B} {g : G.₁ B C} → Htpy (cut f g) (cut f g))
  where
  open G renaming (₀ to Ob; ₁ to _~>_)
  private
    _∙_ = cut; infixr 40 _∙_

    --path : ∀ {A B}




record is-virtual-graph {u v} w (G : Graph u v) : Type (u ⊔ v ⊔ w ₊) where
  no-eta-equality
  private module G = Graph G; _~>_ = G.₁
  field
    ₂ : ∀ {x y} → x ~> y → x ~> y → Type w
    concat : ∀ {x y z} → x ~> y → y ~> z → x ~> z
  private _=>_ = ₂; _∙_ = concat; infixr 40 _∙_
  field
    crefl : ∀ {x y z} {f : x ~> y} {g : y ~> z} → concat f g => concat f g
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
  crefl = V.crefl
  composites-prop = V.composites-prop

  hcenter : ∀ {x y z} {f : x ~> y} {g : y ~> z} → Σ s ∶ (x ~> z) , f ∙ g => s
  hcenter {f} {g} = f ∙ g , crefl

  to-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
          → f ∙ g => s → f ∙ g ＝ s
  to-path p i = composites-prop (_ , crefl) (_ , p) i .fst

  to-pathp : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
           → (p : f ∙ g => s) → PathP (λ i → (f ∙ g) => to-path p i) crefl p
  to-pathp p i = composites-prop (_ , crefl) (_ , p) i .snd

  loop : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z} → f ∙ g => s → s => s
  loop {s} = λ α → transport (λ i → to-path α i => s) α

  lift-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {r s : x ~> z}
            → f ∙ g => r → r ＝ s →  r => s
  lift-path {r} {s} α p = transport (λ i → r => p i) (loop α)

  eql-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {r s : x ~> z}
            → f ∙ g => r → f ∙ g => s → r => s
  eql-path f g = lift-path f (cat (sym (to-path f)) (to-path g))

  -- weak-hconcat : ∀ {x y z} {s1 r1 : x ~> y} {s2 r2 : y ~> z}
  --           → {f : x ~> y} {g : y ~> z}
  --           → f ∙ g => s1 ∙ s2
  --           → f ∙ g => r1 ∙ r2
  --           → s1 ∙ s2 => r1 ∙ r2
  -- weak-hconcat = eql-path

   -- weak-assoc : {s1 : x ~> y} {s2 : y ~> z}
   --        → f ∙ g => s1
   --        → h ∙ k => s2
   --        → s1 ∙ h ∙ k => (f ∙ g) ∙ s2
   -- weak-assoc H K =
   --    transport (λ i → (to-path H i ∙ h ∙ k) => ((f ∙ g) ∙ to-path K i)) crefl

  module encode-decode {x y z} {f : x ~> y} {g : y ~> z} where
    encode : ∀ {s} → f ∙ g ≡ s → f ∙ g => s
    encode p = transport (λ i → f ∙ g => p i) crefl

    decode : ∀ {s} → f ∙ g => s → f ∙ g ≡ s
    decode = to-path

    -- The key fillers for the equivalence
    encode-filler : ∀ {s} (p : f ∙ g ≡ s)
                  → PathP (λ i → f ∙ g => p i) crefl (encode p)
    encode-filler p = transport-filler (λ i → f ∙ g => p i) crefl

  module _ {w x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z} (h : w ~> x) where
    apl : f ∙ g => s → h ∙ f ∙ g => h ∙ s
    apl α = transport (λ i → (h ∙ (f ∙ g)) => (h ∙ to-path α i)) crefl

    apl-filler : (α : f ∙ g => s) → PathP (λ i → (h ∙ (f ∙ g)) => (h ∙ to-path α i)) crefl (apl α)
    apl-filler α = transport-filler (λ i → (h ∙ (f ∙ g)) => (h ∙ to-path α i)) crefl

    apl-prop : (α : f ∙ g => s)
             → (γ : h ∙ (f ∙ g) => h ∙ s)  -- any lift
             → (h ∙ s , apl α) ≡ (h ∙ s , γ)
    apl-prop α γ = composites-prop _ _

  module _ {w x y z} {f : w ~> x} {g : x ~> y} {s : w ~> y} (h : y ~> z) where
    apr : f ∙ g => s → (f ∙ g) ∙ h => s ∙ h
    apr α = transport (λ i → (f ∙ g) ∙ h => to-path α i ∙ h) crefl

    apr-filler : (α : f ∙ g => s) → PathP (λ i → (f ∙ g) ∙ h => to-path α i ∙ h) crefl (apr  α)
    apr-filler α = transport-filler (λ i → (f ∙ g) ∙ h => to-path α i ∙ h) crefl

    apr-prop : (α : f ∙ g => s)
             → (γ : (f ∙ g) ∙ h => s ∙ h)
             → (s ∙ h , apr α) ≡ (s ∙ h , γ)
    apr-prop α γ = composites-prop _ _

  composites-contr : ∀ {x y z} (f : x ~> y) (g : y ~> z) → is-contr (Σ s ∶ x ~> z , f ∙ g => s)
  composites-contr f g .center = _ , crefl
  composites-contr f g .paths x i = to-path (x .snd) i , to-pathp (x .snd) i

  J-composite : ∀ {x y z} {f : x ~> y} {g : y ~> z}
              → (P : (s : x ~> z) (α : f ∙ g => s) → Type)
              → P (f ∙ g) crefl
              → (s : x ~> z) (α : f ∙ g => s) → P s α
  J-composite P base s α = transport (λ i → P (to-path α i) (to-pathp α i)) base

  weak-hsym : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
            → f ∙ g => s → s => f ∙ g
  weak-hsym {s} α = subst (s =>_) (sym (to-path α)) (loop α)

  weak-vconcat : ∀ {w x y z} {f : w ~> x} {f' : x ~> z} {g : w ~> y} {g' : y ~> z} {s : w ~> z}
               → f ∙ f' => g ∙ g' → g ∙ g' => s → f ∙ f' => s
  weak-vconcat {f} {f'} H K = subst (f ∙ f' =>_) (to-path K) H

  module Overlap {w x y z} {f : w ~> x} {g : x ~> y} {h : y ~> z} where
    lwhisk :  {s : w ~> y} → f ∙ g => s → (f ∙ g) ∙ h => s ∙ h
    lwhisk H = transport (λ i → (f ∙ g) ∙ h => to-path H i ∙ h) crefl

    lwhisk-op : {s : w ~> y} → f ∙ g => s → s ∙ h => (f ∙ g) ∙ h
    lwhisk-op H = transport (λ i → to-path H i ∙ h => (f ∙ g) ∙ h) crefl

    -- Abstract right overlap on target bracket
    rwhisk :  {r : x ~> z} → g ∙ h => r → f ∙ (g ∙ h) => f ∙ r
    rwhisk K = transport (λ i → f ∙ (g ∙ h) => f ∙ to-path K i) crefl

    rwhisk-op : {r : x ~> z} → g ∙ h => r → f ∙ r => f ∙ (g ∙ h)
    rwhisk-op K = transport (λ i → f ∙ to-path K i => f ∙ (g ∙ h)) crefl

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
