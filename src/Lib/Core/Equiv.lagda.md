Lane Biocini
October 23, 2025

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Core.Equiv where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Kan
open import Lib.Core.Sub
open import Lib.Core.Type
open import Lib.Core.Transport

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    eqv-fibers : (y : B) → is-contr (fiber f y)

open is-equiv public
_≃_ Equiv : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ {A = A → B} is-equiv; infix 6 _≃_
Equiv = _≃_
{-# BUILTIN EQUIV _≃_ #-}

eqvtofun : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqvtofun e = fst e
{-# BUILTIN EQUIVFUN eqvtofun #-}

equiv-proof : ∀ {u v} (T : Type u) (A : Type v) (w : T ≃ A) (a : A)
            → ∀ φ (u : Partial φ (fiber (w .fst) a)) → fiber (w .fst) a [ φ ↦ u ]
equiv-proof {u} {v} T A w a = is-contr→extend (eqv-fibers (w .snd) a)
{-# BUILTIN EQUIVPROOF equiv-proof #-}

record is-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    sec : (x : A) → inv (f x) ≡ x
    retr : (y : B) → f (inv y) ≡ y

-- Helper to construct is-qinv
qinv : ∀ {u v} {A : Type u} {B : Type v}
    → (f : A → B) (g : B → A)
    → (sec : (x : A) → g (f x) ≡ x)
    → (retr : (y : B) → f (g y) ≡ y)
    → is-qinv f
qinv f g sec retr .is-qinv.inv = g
qinv f g sec retr .is-qinv.sec = sec
qinv f g sec retr .is-qinv.retr = retr


-- I closely followed the argument from 1lab, in I believe their fiberwise equiv module
module qinv {u v} {A : Type u} {B : Type v} {f : A → B} (e : is-qinv f) where
  private
    g = e .is-qinv.inv
    η = e .is-qinv.sec
    ε = e .is-qinv.retr

  module _ {y : B} ((x , p) : fiber f y) where
    faces0 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces0 i = λ where
      k (i = i0) → g y
      k (i = i1) → η (g y) k
      k (k = i0) → g (ε y (~ i))

    faces1 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces1 i = λ where
      k (i = i0) → g y
      k (i = i1) → η x k
      k (k = i0) → g (p (~ i))

    private
      π₀ : g y ≡ g y
      π₀ i = hcomp (∂ i) (faces0 i)

      θ₀ : Square refl (ap g (sym (ε y))) (η (g y)) π₀
      θ₀ i j = hfill (∂ i) j (faces0 i)

      π₁ : g y ≡ x
      π₁ i = hcomp (∂ i) (faces1 i)

      θ₁ : Square refl (ap g (sym p)) (η x)  π₁
      θ₁ i j = hfill (∂ i) j (faces1 i)

      fiber-sys : (i j : I) → Partial (∂ i ∨ ~ j) A
      fiber-sys i = λ where
        j (i = i0) → π₀ j
        j (i = i1) → π₁ j
        j (j = i0) → g y

      path : g y ≡ x
      path i = hcomp (∂ i) (fiber-sys i)

      fiber-filler : Square π₀ refl π₁ path
      fiber-filler i j = hfill (∂ i) j (fiber-sys i)

      ι : Square (ap g (ε y)) (ap (λ z → g (f z)) path) (ap g p) refl
      ι i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → θ₀ (~ j) (~ k)
        k (i = i1) → θ₁ (~ j) (~ k)
        k (j = i0) → η (path i) (~ k)
        k (j = i1) → g y
        k (k = i0) → fiber-filler i (~ j)

      filler : Square (ε y) (ap f path) p refl
      filler i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → ε (ε y j) k
        k (i = i1) → ε (p j) k
        k (j = i0) → ε (f (path i)) k
        k (j = i1) → ε y k
        k (k = i0) → f (ι i j)

    unit : g (f x) ≡ x
    unit i = hcomp (∂ i) λ where
      j (i = i0) → g (f x)
      j (i = i1) → path j
      j (j = i0) → g (p i)

    counit : f (g y) ≡ y
    counit = ε y

    private
      φ : Square refl p (sym (ε y)) (ap f (sym path))
      φ = Triangle.post (sym (ε y)) (ap f path) (sym p) (rrotate filler)

    adj : ap f unit ≡ ε (f x)
    adj i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → f (cat.fill (ap g p) path j k)
      k (i = i1) → ε (p (~ k)) j
      k (j = i0) → f (g (p (i ∧ ~ k)))
      k (j = i1) → φ (~ k) (~ i)
      k (k = i0) → conn (ap (λ z → (f (g z))) p) (ε y) i j

    fiber-path : Path (fiber f y) (g y , ε y) (x , p)
    fiber-path i .fst = path i
    fiber-path i .snd = filler i

  contr : (y : B) → is-contr (fiber f y)
  contr y .center = g y , ε y
  contr y .paths = fiber-path

  to-equiv : is-equiv f
  to-equiv .eqv-fibers = contr

iso→equiv : ∀ {u v} {A : Type u} {B : Type v}
          → (f : A → B) (g : B → A)
          → (sec : (x : A) → g (f x) ≡ x)
          → (retr : (y : B) → f (g y) ≡ y)
          → A ≃ B
iso→equiv f g sec retr = f , qinv.to-equiv (qinv f g sec retr)

module Equiv {u v} {A : Type u} {B : Type v} (e : A ≃ B) where
  private module M = is-equiv (e .snd)
  fwd = e .fst

  c : (y : B) → fiber fwd y
  c y = M.eqv-fibers y .center

  inv : B → A
  inv y = c y .fst

  fibers : {y : B} (fb : fiber fwd y) → c y ≡ fb
  fibers {y} = M.eqv-fibers y .paths

  unit : (x : A) → inv (fwd x) ≡ x
  unit x i = fibers (x , λ _ → fwd x) i .fst

  counit :  (y : B) → fwd (inv y) ≡ y
  counit y = c y .snd

-- From 1lab: this helper is for functions f, g that cancel each other, up to
-- definitional equality, without any case analysis on the argument:
strict-fibers : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
              → (g : B → A) (b : B)
              → Σ f0 ∶ fiber f (f (g b))
              , ((f1 : fiber f b)
                     → Path (fiber f (f (g b))) f0 (g (f (f1 .fst)) , ap (f ∘ g) (f1 .snd)))
strict-fibers {f = f} g b .fst = (g b , refl)
strict-fibers {f = f} g b .snd (a , p) i = (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

id-equiv : ∀ {u} {A : Type u} → is-equiv (idfun A)
id-equiv .eqv-fibers y .center = y , refl
id-equiv .eqv-fibers y .paths (x , p) i = p (~ i) , λ j → p (~ i ∨ j)

equiv : ∀ {u} {A : Type u} → A ≃ A
equiv .fst = id
equiv .snd = id-equiv

esym : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → B ≃ A
esym e = iso→equiv E.inv E.fwd E.counit E.unit where module E = Equiv e

_∙e_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
     → A ≃ B → B ≃ C → A ≃ C
e ∙e f = iso→equiv fwd bwd sec retr
  where
    module E = Equiv e
    module F = Equiv f

    fwd : _
    fwd a = F.fwd (E.fwd a)

    bwd : _
    bwd c = E.inv (F.inv c)

    sec : _
    sec a = ap E.inv (F.unit (E.fwd a)) ∙ E.unit a

    retr : _
    retr c = ap F.fwd (E.counit (F.inv c)) ∙ F.counit c

infixr 9 _∙e_

Σ-×-swap : ∀ {u v w z} {A : Type u} {B : Type v} {P : A → Type w} {Q : B → Type z}
         → (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂) ≃ ((Σ P) × (Σ Q))
Σ-×-swap = iso→equiv fwd bwd (λ _ → refl) (λ _ → refl)
  where
    fwd : _
    fwd ((s₁ , s₂) , (p , q)) = (s₁ , p) , (s₂ , q)

    bwd : _
    bwd ((s₁ , p) , (s₂ , q)) = (s₁ , s₂) , (p , q)

×-Σ-swap : ∀ {u v w z} {A : Type u} {B : Type v} {P : A → Type w} {Q : B → Type z}
         → ((Σ P) × (Σ Q)) ≃ (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂)
×-Σ-swap = iso→equiv fwd bwd (λ _ → refl) (λ _ → refl)
  where
    fwd : _
    fwd ((s₁ , p) , (s₂ , q)) = (s₁ , s₂) , (p , q)

    bwd : _
    bwd ((s₁ , s₂) , (p , q)) = (s₁ , p) , (s₂ , q)

Σ-equiv-snd : ∀ {u v w} {A : Type u} {P : A → Type v} {Q : A → Type w}
            → (∀ a → P a ≃ Q a) → Σ P ≃ Σ Q
Σ-equiv-snd e = iso→equiv fwd bwd sec retr
  where
    fwd : _
    fwd (a , p) = a , e a .fst p

    bwd : _
    bwd (a , q) = a , Equiv.inv (e a) q

    sec : _
    sec (a , p) = ap (a ,_) (Equiv.unit (e a) p)

    retr : _
    retr (a , q) = ap (a ,_) (Equiv.counit (e a) q)

×-path-equiv : ∀ {u v} {A : Type u} {B : Type v} {x y : A × B}
             → (x ≡ y) ≃ ((x .fst ≡ y .fst) × (x .snd ≡ y .snd))
×-path-equiv = iso→equiv fwd bwd (λ _ → refl) (λ _ → refl)
  where
    fwd : _
    fwd p = ap fst p , ap snd p

    bwd : _
    bwd (p , q) i = p i , q i

Σ-fiber-swap : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w} {D : Type z}
                  {f : A → C} {g : B → D} {α : C} {α' : D}
              → (Σ (β , β') ∶ A × B , (f β , g β') ≡ (α , α'))
              ≃ ((Σ β ∶ A , f β ≡ α) × (Σ β' ∶ B , g β' ≡ α'))
Σ-fiber-swap = Σ-equiv-snd (λ _ → ×-path-equiv) ∙e Σ-×-swap
