Lane Biocini

```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Virt.Morphism where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Type
open import Lib.Core.HLevel
open import Lib.Core.Kan
open import Lib.Core.Cast
open import Lib.Virt.Base
open import Lib.Virt.Composite

module _ {u} {Γ : Type u} ⦃ V : Virtual Γ ⦄ where
  open Virtual V

  module _ (C : Γ) where
    private
      infix 6 _~>_ _=>_
      _~>_ = hom C
      _=>_ = hom2 C
      _⨾_ = cut
      _⊚_ = vcut; infixr 9 _⨾_ _⊚_
      _●_ = hcut; infixr 8 _●_

    -- generalizing from fibers in the identity type, hence fibroid
    fibroid : ∀ {x y z} → x ~> y → x ~> z → Type (l₁ ⊔ l₂)
    fibroid {y} {z} f s = Σ k ∶ y ~> z , f ⨾ k => s

    cofibroid : ∀ {w x y} → x ~> y → w ~> y → Type (l₁ ⊔ l₂)
    cofibroid {w} {x} f s = Σ h ∶ w ~> x , h ⨾ f => s

    2-fibroid : ∀ {x y} {f g s : x ~> y} → f => g → f => s → Type _
    2-fibroid {g} {s} α β = Σ φ ∶ g => s , α ⊚ φ ≡ β

    2-cofibroid : ∀ {x y} {f g s : x ~> y} → g => s → f => s → Type _
    2-cofibroid {f} {g} α β = Σ φ ∶ f => g , φ ⊚ α ≡ β

    weakly-right-divisible : ∀ {x y z} → x ~> y → x ~> z → Type (l₁ ⊔ l₂)
    weakly-right-divisible f s = is-prop (fibroid f s)

    weakly-left-divisible : ∀ {w x y} → x ~> y → w ~> y → Type (l₁ ⊔ l₂)
    weakly-left-divisible f s = is-prop (cofibroid f s)

    right-divisible : ∀ {x y z} → x ~> y → x ~> z → Type (l₁ ⊔ l₂)
    right-divisible f s = is-contr (fibroid f s)

    left-divisible : ∀ {w x y} → x ~> y → w ~> y → Type (l₁ ⊔ l₂)
    left-divisible f s = is-contr (cofibroid f s)

    record is-isomorphism {x y} (f : x ~> y) : Type (l₀ ⊔ l₁ ⊔ l₂) where
      no-eta-equality
      field
        divl : ∀ {w} (s : w ~> y) → left-divisible f s
        divr : ∀ {z} (s : x ~> z) → right-divisible f s

      divl-unique : ∀ {w} (s : w ~> y) → weakly-left-divisible f s
      divl-unique s = is-contr→is-prop (divl s)

      divr-unique : ∀ {z} (s : x ~> z) → weakly-right-divisible f s
      divr-unique s = is-contr→is-prop (divr s)

    record is-homotopy {x y} {s r : x ~> y} (H : s => r) : Type (l₂ ⊔ l₁) where
      field
        divl : ∀ {k} (S : s => k) → is-contr (Σ G ∶ r => k , H ⊚ G ≡ S)
        divr : ∀ {h} (S : h => r) → is-contr (Σ F ∶ h => s , F ⊚ H ≡ S)

    is-isomorphism-is-prop : ∀ {x y} (q : x ~> y) → is-prop (is-isomorphism q)
    is-isomorphism-is-prop q p₁ p₂ i .is-isomorphism.divl s =
      is-contr-is-prop (cofibroid q s) (p₁ .is-isomorphism.divl s) (p₂ .is-isomorphism.divl s) i
    is-isomorphism-is-prop q p₁ p₂ i .is-isomorphism.divr s =
      is-contr-is-prop (fibroid q s) (p₁ .is-isomorphism.divr s) (p₂ .is-isomorphism.divr s) i

    is-homotopy-is-prop : ∀ {x y} {s r : x ~> y} (H : s => r) → is-prop (is-homotopy H)
    is-homotopy-is-prop H p₁ p₂ i .is-homotopy.divl s =
      is-contr-is-prop _ (p₁ .is-homotopy.divl s) (p₂ .is-homotopy.divl s) i
    is-homotopy-is-prop H p₁ p₂ i .is-homotopy.divr s =
      is-contr-is-prop _ (p₁ .is-homotopy.divr s) (p₂ .is-homotopy.divr s) i

    ceqv-homotopy : ∀ {x y z} {f : x ~> y} {g : y ~> z} → is-homotopy (ceqv {f = f} {g})
    ceqv-homotopy .is-homotopy.divl = ceqv-divl
    ceqv-homotopy .is-homotopy.divr = ceqv-divr

    divr→lcancel : ∀ {x y z} {f : x ~> y} {k₁ k₂ : y ~> z}
                 → (∀ s → is-contr (fibroid f s))
                 → f ⨾ k₁ => f ⨾ k₂ → k₁ ≡ k₂
    divr→lcancel {f = f} {k₁} {k₂} f-div σ =
      ap fst (is-contr→is-prop (f-div (cut f k₂)) (k₁ , σ) (k₂ , ceqv))

    divl→rcancel : ∀ {w x y} {g : x ~> y} {h₁ h₂ : w ~> x}
                 → (∀ s → left-divisible g s)
                 → h₁ ⨾ g => h₂ ⨾ g → h₁ ≡ h₂
    divl→rcancel {g = g} {h₁} {h₂} g-div σ =
      ap fst (is-contr→is-prop (g-div (cut h₂ g)) (h₁ , σ) (h₂ , ceqv))

    homotopy→lcancel : ∀ {x y} {s r k : x ~> y} {H : s => r} {G₁ G₂ : r => k}
                     → is-homotopy H → H ⊚ G₁ ≡ H ⊚ G₂ → G₁ ≡ G₂
    homotopy→lcancel {H} {G₁} {G₂} H-htpy p =
      ap fst (is-contr→is-prop (H-htpy .is-homotopy.divl (H ⊚ G₂)) (G₁ , p) (G₂ , refl))

    homotopy→rcancel : ∀ {x y} {h s r : x ~> y} {H : s => r} {F₁ F₂ : h => s}
                     → is-homotopy H → F₁ ⊚ H ≡ F₂ ⊚ H → F₁ ≡ F₂
    homotopy→rcancel {H = H} {F₁} {F₂} H-htpy p =
      ap fst (is-contr→is-prop (H-htpy .is-homotopy.divr (F₂ ⊚ H)) (F₁ , p) (F₂ , refl))

    iso→lcancel : ∀ {x y z} {f : x ~> y} {k₁ k₂ : y ~> z}
                → is-isomorphism f → f ⨾ k₁ => f ⨾ k₂ → k₁ ≡ k₂
    iso→lcancel f-iso = divr→lcancel (λ s → f-iso .is-isomorphism.divr s)

    iso→rcancel : ∀ {w x y} {g : x ~> y} {h₁ h₂ : w ~> x}
                → is-isomorphism g → h₁ ⨾ g => h₂ ⨾ g → h₁ ≡ h₂
    iso→rcancel g-iso = divl→rcancel (λ s → g-iso .is-isomorphism.divl s)

    idem-wthunk-unique : ∀ {x} (q q' : x ~> x)
                      → (cq : is-isomorphism q) (cq' : is-isomorphism q')
                      → (idem-q : q ⨾ q => q)
                      → (let c = cq' .is-isomorphism.divl q .center .fst)
                      → ((c ⨾ q') ⨾ q') => (c ⨾ q')
                      → q ≡ q'
    idem-wthunk-unique {x} q q' cq cq' idem-q thk = ap fst (prop (q , idem-q) (q' , qq'=>q)) where
      module cq' = is-isomorphism cq'
      prop = is-contr→is-prop (cq .is-isomorphism.divr q)

      c : x ~> x
      c = cq'.divl q .center .fst

      cq'=>q : c ⨾ q' => q
      cq'=>q = cq'.divl q .center .snd

      qq'=>q : q ⨾ q' => q
      qq'=>q = cconcat C (lwhisk-op C cq'=>q) (cconcat C thk cq'=>q)

    module IdempotentEquivalences where

      record is-idem-equiv {x} (i : x ~> x) : Type (l₀ ⊔ l₁ ⊔ l₂) where
        no-eta-equality
        field
          iso : is-isomorphism i
          i-wlinear : ∀ {y} (f : x ~> y) → i ⨾ (i ⨾ f) => i ⨾ f
          i-wthunkable : ∀ {w} (f : w ~> x) → (f ⨾ i) ⨾ i => f ⨾ i

        private module iso = is-isomorphism iso

        -- Key: cofibroid i (i ⨾ f) is a prop, so these two inhabitants are equal
        -- (f, csym (i-wlinear f) ⊚ i-wlinear f) and (i ⨾ f, i-wlinear f)
        lin-coh : ∀ {y} (f : x ~> y)
                → (f , csym C (i-wlinear f) ⊚ i-wlinear f) ≡ (i ⨾ f , i-wlinear f)
        lin-coh f = is-contr→is-prop (iso.divr (i ⨾ f)) _ _

        -- Extract the path: i ⨾ f ≡ f
        unitl-path : ∀ {y} (f : x ~> y) → i ⨾ f ≡ f
        unitl-path f = ap fst (sym (lin-coh f))

        -- Transport to get the 2-cell
        unitl : ∀ {y} (f : x ~> y) → i ⨾ f => f
        unitl f = transport (λ j → i ⨾ f => unitl-path f j) (csym C (i-wlinear f) ⊚ i-wlinear f)

        -- Dual: fibroid i (f ⨾ i) is a prop
        thk-coh : ∀ {w} (f : w ~> x)
                → (f , csym C (i-wthunkable f) ⊚ i-wthunkable f) ≡ (f ⨾ i , i-wthunkable f)
        thk-coh f = is-contr→is-prop (iso.divl (f ⨾ i)) _ _

        unitr-path : ∀ {w} (f : w ~> x) → f ⨾ i ≡ f
        unitr-path f = ap fst (sym (thk-coh f))

        unitr : ∀ {w} (f : w ~> x) → f ⨾ i => f
        unitr f = transport (λ j → f ⨾ i => unitr-path f j) (csym C (i-wthunkable f) ⊚ i-wthunkable f)

        -- Idempotence
        idem : i ⨾ i => i
        idem = unitl i

        idem-path : i ⨾ i ≡ i
        idem-path = unitl-path i

      -- Uniqueness via unit laws
      idem-equiv-unique : ∀ {x} (i j : x ~> x)
                        → is-idem-equiv i → is-idem-equiv j
                        → i ≡ j
      idem-equiv-unique i j ie je = sym (is-idem-equiv.unitr-path je i) ∙ is-idem-equiv.unitl-path ie j

      is-idem-equiv-is-prop : ∀ {x} (i : x ~> x) → is-prop (is-idem-equiv i)
      is-idem-equiv-is-prop i ie₁ ie₂ = goal where
        open is-idem-equiv

        iso-path : iso ie₁ ≡ iso ie₂
        iso-path = is-isomorphism-is-prop i _ _

        -- i-wlinear f is uniquely determined: both are connected to ceqv
        -- via THE path in the prop Σ s, i ⨾ (i ⨾ f) => s
        wlin-path : ∀ {y} (f : _ ~> y) → i-wlinear ie₁ f ≡ i-wlinear ie₂ f
        wlin-path f = ? where
          -- Both (i ⨾ f, i-wlinear ie₁ f) and (i ⨾ f, i-wlinear ie₂ f)
          -- equal (i ⨾ (i ⨾ f), ceqv) in the prop total space
          p₁ : (i ⨾ (i ⨾ f) , ceqv) ≡ (i ⨾ f , i-wlinear ie₁ f)
          p₁ = cut-unique ? _ _

          p₂ : (i ⨾ (i ⨾ f) , ceqv) ≡ (i ⨾ f , i-wlinear ie₂ f)
          p₂ = cut-unique ? _ _

          -- The total space is a prop, so p₁ ≡ p₂
          path : (i ⨾ f , i-wlinear ie₁ f) ≡ (i ⨾ f , i-wlinear ie₂ f)
          path = sym p₁ ∙ p₂

        wthk-path : ∀ {w} (f : w ~> _) → i-wthunkable ie₁ f ≡ i-wthunkable ie₂ f
        wthk-path f = ap snd path where
          p₁ : ((f ⨾ i) ⨾ i , ceqv) ≡ (f ⨾ i , i-wthunkable ie₁ f)
          p₁ = cut-unique Γ _ _

          p₂ : ((f ⨾ i) ⨾ i , ceqv) ≡ (f ⨾ i , i-wthunkable ie₂ f)
          p₂ = cut-unique Γ _ _

          path : (f ⨾ i , i-wthunkable ie₁ f) ≡ (f ⨾ i , i-wthunkable ie₂ f)
          path = sym p₁ ∙ p₂

        goal : ie₁ ≡ ie₂
        goal k .iso = iso-path k
        goal k .i-wlinear f = wlin-path f k
        goal k .i-wthunkable f = wthk-path f k

      has-idem-equiv-is-prop : ∀ {x} → is-prop (Σ i ∶ x ~> x , is-idem-equiv i)
      has-idem-equiv-is-prop (i , ie) (j , je) =
        Σ-path (idem-equiv-unique i j ie je) (is-idem-equiv-is-prop j _ _)

    open IdempotentEquivalences public
