Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Magmoid.Type

module Cat.Magmoid.Base (M : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv renaming (_≃_ to _≃e_)

open Magmoids M public

module _ {x y} (f : hom x y) where
  is-left-divisible : Type (o ⊔ h)
  is-left-divisible = ∀ {w} → is-equiv (λ (h : hom w x) → h ⨾ f)

  is-right-divisible : Type (o ⊔ h)
  is-right-divisible = ∀ {z} → is-equiv (λ (g : hom y z) → f ⨾ g)

divl→rcancel
  : ∀ {w x y} {g : hom x y} {h₁ h₂ : hom w x}
  → (is-left-divisible g)
  → h₁ ⨾ g ≡ h₂ ⨾ g → h₁ ≡ h₂
divl→rcancel {g = g} {h₁} {h₂} e σ =
  ap fst (is-contr→is-prop (e .eqv-fibers (h₂ ⨾ g))
    (h₁ , σ) (h₂ , refl))

divr→lcancel
  : ∀ {x y z} {f : hom x y} {k₁ k₂ : hom y z}
  → (is-right-divisible f)
  → f ⨾ k₁ ≡ f ⨾ k₂ → k₁ ≡ k₂
divr→lcancel {f = f} {k₁} {k₂} e σ =
  ap fst (is-contr→is-prop (e .eqv-fibers (f ⨾ k₂))
    (k₁ , σ) (k₂ , refl))

is-neutral : ∀ {x y} → hom x y → Type (o ⊔ h)
is-neutral {x} {y} f =
  is-left-divisible f × is-right-divisible f

_≅ˢ_ : ob → ob → Type (o ⊔ h)
x ≅ˢ y = Σ f ∶ hom x y , is-neutral f

associator : ∀ {w x y z} → hom w x → hom x y → hom y z → Type h
associator f g h = f ⨾ (g ⨾ h) ≡ (f ⨾ g) ⨾ h
{-# INLINE associator #-}

is-thunkable : ∀ {w x} → hom w x → Type (o ⊔ h)
is-thunkable {x} f = ∀ {y z} (g : hom x y) (h : hom y z) → associator f g h

is-linear : ∀ {y z} → hom y z → Type (o ⊔ h)
is-linear {y} h = ∀ {w x} (f : hom w x) (g : hom x y) → associator f g h

associativity : Type (o ⊔ h)
associativity
  = ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z) → associator f g h

commutative-sq
  : ∀ {a b c d} (f : hom a b) (g : hom a c) (e : hom b d) (d : hom c d) → Type h
commutative-sq f g e d = f ⨾ e ≡ g ⨾ d

is-neutral-is-prop
  : ∀ {x y} (f : hom x y) → is-prop (is-neutral f)
is-neutral-is-prop f = is-prop-×
  (Πi-is-prop λ _ → is-equiv-is-prop _) (Πi-is-prop λ _ → is-equiv-is-prop _)

infixr 25 _▹_
_▹_
  : ∀ {x y z} {f f' : hom x y}
  → f ≡ f' → (h : hom y z)
  → (f ⨾ h) ≡ (f' ⨾ h)
γ ▹ h = ap (_⨾ h) γ

infixl 26 _◃_
_◃_
  : ∀ {w x y} (h : hom w x)
  → {f f' : hom x y} → f ≡ f'
  → (h ⨾ f) ≡ (h ⨾ f')
h ◃ γ = ap (h ⨾_) γ

nat-sq
  : ∀ {x y z} {f f' : hom x y}
    {g g' : hom y z}
  → (α : f ≡ f') (β : g ≡ g')
  → Square (α ▹ g) (f ◃ β) (α ▹ g') (f' ◃ β)
nat-sq α β i j = α j ⨾ β i

module _ {x} (e : hom x x) where
  lunital runital : Type (o ⊔ h)
  lunital = ∀ {y} (f : hom x y)
    → e ⨾ (e ⨾ f) ≡ e ⨾ f
  runital = ∀ {w} (f : hom w x)
    → (f ⨾ e) ⨾ e ≡ f ⨾ e

  record is-unital : Type (o ⊔ h) where
    field
      neutral : is-neutral e
      lcoh : lunital
      rcoh : runital

module iso {x y} {f : hom x y} (e : is-neutral f) where
  divl : ∀ {z} → hom x z → hom y z
  divl = Equiv.inv (f ⨾_ , e .snd)

  divr : ∀ {w} → hom w y → hom w x
  divr = Equiv.inv (_⨾ f , e .fst)

  divl-is-equiv : ∀ {z} → is-equiv (divl {z})
  divl-is-equiv = sym-equiv (e .snd)

  divr-is-equiv : ∀ {w} → is-equiv (divr {w})
  divr-is-equiv = sym-equiv (e .fst)

  coloop : hom y y
  coloop = divl f

  loop : hom x x
  loop = divr f

  pre-counit : ∀ {z} (g : hom x z)
    → f ⨾ divl g ≡ g
  pre-counit = Equiv.counit (f ⨾_ , e .snd)

  post-counit : ∀ {w} (g : hom w y)
    → divr g ⨾ f ≡ g
  post-counit = Equiv.counit (_⨾ f , e .fst)

  pre-unit : ∀ {z} (g : hom y z)
    → divl (f ⨾ g) ≡ g
  pre-unit = Equiv.unit (f ⨾_ , e .snd)

  post-unit : ∀ {w} (g : hom w x)
    → divr (g ⨾ f) ≡ g
  post-unit = Equiv.unit (_⨾ f , e .fst)

unital : ∀ x → Type (o ⊔ h)
unital x = Σ i ∶ hom x x , is-unital i

module unital {x} ((i , e) : unital x) where
  open is-unital e public
  open iso (e .is-unital.neutral)

  iso-refl : x ≅ˢ x
  iso-refl .fst = i
  iso-refl .snd = neutral

  unit : hom x x
  unit = i

  unitl : ∀ {y} (f : hom x y) → i ⨾ f ≡ f
  unitl {y} f = pcom (pre-unit (i ⨾ f)) (ap divl (lcoh f)) (pre-unit f)

  unitr : ∀ {w} (f : hom w x) → f ⨾ i ≡ f
  unitr {w} f = pcom (post-unit (f ⨾ i)) (ap divr (rcoh f)) (post-unit f)

  idem : i ⨾ i ≡ i
  idem j = cone (unitl i) (unitr i) j j

  iso : is-neutral i
  iso = neutral

  f0 : Path (fiber (_⨾ i) i) (loop , post-counit i) (i , idem)
  f0 = Equiv.fibers ((_⨾ i) , neutral .fst) (i , idem)

  f1 : Path (fiber (i ⨾_) i) (coloop , pre-counit i) (i , idem)
  f1 = Equiv.fibers ((i ⨾_) , neutral .snd) (i , idem)

  loop-coh : loop ≡ i
  loop-coh = ap fst f0

  coloop-coh : coloop ≡ i
  coloop-coh = ap fst f1

unital-unique : ∀ {x} {i j : hom x x} → is-unital i → is-unital j → i ≡ j
unital-unique {x} {i} {j} ui uj =
  sym (unital.unitr (j , uj) i) ∙ unital.unitl (i , ui) j

triangle : ∀ {x y z} (f : hom x y) (g : hom y z)
         → (e : unital y)
         → f ⨾ e .fst ⨾ g ≡ (f ⨾ e .fst) ⨾ g
         → Type h
triangle f g e a0 = a0 ∙ (unitr f ▹ g) ≡ f ◃ (unitl g) where open unital e
{-# INLINE triangle #-}

pentagon
  : ∀ {w x y z a} (f : hom w x) (g : hom x y) (k : hom y z) (l : hom z a)
  → g ⨾ k ⨾ l ≡ (g ⨾ k) ⨾ l
  → f ⨾ (g ⨾ k) ⨾ l ≡ (f ⨾ g ⨾ k) ⨾ l
  → f ⨾ g ⨾ k ≡ (f ⨾ g) ⨾ k
  → f ⨾ g ⨾ k ⨾ l ≡ (f ⨾ g) ⨾ k ⨾ l
  → (f ⨾ g) ⨾ k ⨾ l ≡ ((f ⨾ g) ⨾ k) ⨾ l
  → Type h
pentagon f g k l a0 a1 a2 b0 b1 = (f ◃ a0) ∙ a1 ∙ (a2 ▹ l) ≡ b0 ∙ b1
{-# INLINE pentagon #-}

-- record is-pullback {b c d ρ} {f : hom b d} {g : hom c d} {π₁ : hom ρ b} {π₂ : hom ρ c}
--   (pb : commutative-sq π₁ π₂ f g) : Type (o ⊔ h) where
--   no-eta-equality
--   field
--     universal
--       : ∀ {a} (α : hom a b) (β : hom a c) → commutative-sq α β f g
--       → is-contr (Σ h ∶ hom a ρ , (h ⨾ π₁ ≡ α) × (h ⨾ π₂ ≡ β))

--   gap : ∀ {a} (α : hom a b) (β : hom a c) → commutative-sq α β f g → hom a ρ
--   gap α β s = universal α β s .center .fst

--   gap-π₁
--     : ∀ {a} (α : hom a b) (β : hom a c) (s : commutative-sq α β f g)
--     → gap α β s ⨾ π₁ ≡ α
--   gap-π₁ α β s = universal α β s .center .snd .fst

--   gap-π₂
--     : ∀ {a} (α : hom a b) (β : hom a c) (s : commutative-sq α β f g)
--     → gap α β s ⨾ π₂ ≡ β
--   gap-π₂ α β s = universal α β s .center .snd .snd

-- {-# INLINE is-pullback.constructor #-}

-- record pullback {b c d} (f : hom b d) (g : hom c d) : Type (o ⊔ h) where
--   no-eta-equality
--   field
--     apex   : ob
--     π₁     : hom apex b
--     π₂     : hom apex c
--     square : commutative-sq π₁ π₂ f g
--     is-pb  : is-pullback square
--   open is-pullback is-pb public

-- {-# INLINE pullback.constructor #-}
