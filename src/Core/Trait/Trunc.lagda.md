Truncation level automation via instance resolution.

This module provides the `Trunc` trait for h-level automation, extracted from
Core.HLevel. The mathematical definitions (`is-hlevel`, `is-prop`, etc.) remain
in Core.HLevel; this module provides the automation layer.

The H-Level automation machinery in this module is largely derived from 1Lab
(Amélia Liao et al.), with additional influence from Chen's semicategories-with-
identities formalization.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Trait.Trunc where

open import Core.Type
open import Core.Base
open import Core.Sub
open import Core.Kan
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base using (_+_)
import Core.Data.Nat.Properties as NatP
open import Core.Path
open import Core.Equiv
open import Core.Transport

private variable
  ℓ ℓ' : Level
  A B : Type ℓ
  n k : Nat

-- Re-export is-hlevel from Core.HLevel to avoid import cycles
-- We inline the definitions here since Core.HLevel will depend on us

is-hlevel : Nat → Type ℓ → Type ℓ
is-hlevel Z A = is-contr A
is-hlevel (S Z) A = is-prop A
is-hlevel (S (S n)) A = (x y : A) → is-hlevel (S n) (x ≡ y)

-- Core lemmas needed for instances

is-hlevel-suc : is-hlevel n A → is-hlevel (S n) A
is-hlevel-suc {n = Z} c = is-contr→is-prop c
is-hlevel-suc {n = S Z} p x y = is-prop→is-set p x y
is-hlevel-suc {n = S (S n)} hl x y = is-hlevel-suc (hl x y)

is-hlevel-+ : (n k : Nat) → is-hlevel n A → is-hlevel (n + k) A
is-hlevel-+ {A = A} n Z hl = subst (λ m → is-hlevel m A) (sym (NatP.add.unitr n)) hl
is-hlevel-+ {A = A} n (S k) hl =
  subst (λ m → is-hlevel m A) (sym (NatP.add.+suc n k))
    (is-hlevel-suc (is-hlevel-+ n k hl))

is-contr→is-hlevel : (n : Nat) → is-contr A → is-hlevel n A
is-contr→is-hlevel Z c = c
is-contr→is-hlevel (S n) c = is-hlevel-suc (is-contr→is-hlevel n c)

is-prop→is-hlevel-suc : is-prop A → is-hlevel (S n) A
is-prop→is-hlevel-suc {n = Z} p = p
is-prop→is-hlevel-suc {n = S Z} p x y = is-prop→is-set p x y
is-prop→is-hlevel-suc {n = S (S n)} p x y =
  is-prop→is-hlevel-suc {n = S n} (is-prop→is-set p x y)

is-hlevel-is-prop : (n : Nat) → is-prop (is-hlevel n A)
is-hlevel-is-prop Z = is-contr-is-prop _
is-hlevel-is-prop (S Z) = is-prop-is-prop _
is-hlevel-is-prop (S (S n)) p q i x y = is-hlevel-is-prop (S n) (p x y) (q x y) i

-- Structural lemmas

retract→is-hlevel : (n : Nat)
                  → (f : A → B) (g : B → A)
                  → is-left-inverse f g
                  → is-hlevel n A → is-hlevel n B
retract→is-hlevel Z f g r c .center = f (c .center)
retract→is-hlevel Z f g r c .paths y = ap f (c .paths (g y)) ∙ r y
retract→is-hlevel (S Z) f g r p x y = sym (r x) ∙ ap f (p (g x) (g y)) ∙ r y
retract→is-hlevel (S (S n)) f g r hl x y =
  retract→is-hlevel (S n) fwd (ap g) retract-proof (hl (g x) (g y))
  where
    fwd : g x ≡ g y → x ≡ y
    fwd p = sym (r x) ∙ ap f p ∙ r y

    retract-proof : is-left-inverse fwd (ap g)
    retract-proof q = J (λ y' q' → sym (r x) ∙ ap f (ap g q') ∙ r y' ≡ q')
      (ap (sym (r x) ∙_) (eqvl (r x)) ∙ invl (r x)) q

Path-is-hlevel : {x y : A} → is-hlevel (S n) A → is-hlevel n (x ≡ y)
Path-is-hlevel {n = Z} p = prop-inhabited→is-contr (is-prop→is-set p _ _) (p _ _)
Path-is-hlevel {n = S n} hl = hl _ _

PathP-is-hlevel : ∀ {A : I → Type ℓ} {x : A i0} {y : A i1}
                → is-hlevel (S n) (A i1) → is-hlevel n (PathP A x y)
PathP-is-hlevel {A = A} {x = x} {y = y} hl =
  subst (is-hlevel _) pathp-eq (Path-is-hlevel {x = coe01 A x} {y = y} hl)
  where
    pathp-eq : (coe01 A x ≡ y) ≡ PathP A x y
    pathp-eq i = PathP (∂.contract A (~ i)) (coe-filler A x (~ i)) y

Π-is-prop : {B : A → Type ℓ'}
          → ((a : A) → is-prop (B a))
          → is-prop ((a : A) → B a)
Π-is-prop prop f g i = λ a → prop a (f a) (g a) i

Πi-is-prop : {B : A → Type ℓ'}
           → ((a : A) → is-prop (B a))
           → is-prop ({a : A} → B a)
Πi-is-prop prop f g i {a} = prop a f g i

Π-is-hlevel : {B : A → Type ℓ'} (n : Nat)
            → ((a : A) → is-hlevel n (B a))
            → is-hlevel n ((a : A) → B a)
Π-is-hlevel Z hl .center a = hl a .center
Π-is-hlevel Z hl .paths f i a = hl a .paths (f a) i
Π-is-hlevel (S Z) hl = Π-is-prop hl
Π-is-hlevel (S (S n)) hl f g =
  retract→is-hlevel (S n) funext happly (λ _ → refl)
    (Π-is-hlevel (S n) (λ a → hl a (f a) (g a)))

Σ-prop-path : ∀ {B : A → Type ℓ'} (bp : ∀ x → is-prop (B x))
            → {x y : Σ B}
            → (x .fst ≡ y .fst) → x ≡ y
Σ-prop-path bp {x} {y} p i =
  p i , is-prop→PathP (λ i → bp (p i)) (x .snd) (y .snd) i

Σ-is-prop : {B : A → Type ℓ'}
          → is-prop A → (∀ a → is-prop (B a)) → is-prop (Σ B)
Σ-is-prop aprop bprop (a₁ , b₁) (a₂ , b₂) = Σ-prop-path bprop (aprop a₁ a₂)

Σ-is-hlevel : {B : A → Type ℓ'} (n : Nat)
            → is-hlevel n A → ((a : A) → is-hlevel n (B a))
            → is-hlevel n (Σ B)
Σ-is-hlevel Z acontr bcontr .center =
  acontr .center , bcontr (acontr .center) .center
Σ-is-hlevel Z acontr bcontr .paths (a , b) i =
  acontr .paths a i
  , is-prop→PathP (λ i → is-contr→is-prop (bcontr (acontr .paths a i)))
      (bcontr (acontr .center) .center) b i
Σ-is-hlevel (S Z) aprop bprop = Σ-is-prop aprop bprop
Σ-is-hlevel {B = B} (S (S n)) ahl bhl (a₁ , b₁) (a₂ , b₂) =
  retract→is-hlevel (S n) fwd bwd (λ _ → refl) inner
  where
    Σ-Path : Type _
    Σ-Path = Σ p ∶ a₁ ≡ a₂ , PathP (λ i → B (p i)) b₁ b₂

    fwd : Σ-Path → (a₁ , b₁) ≡ (a₂ , b₂)
    fwd (p , bp) i = p i , bp i

    bwd : (a₁ , b₁) ≡ (a₂ , b₂) → Σ-Path
    bwd q = (λ i → q i .fst) , (λ i → q i .snd)

    inner : is-hlevel (S n) Σ-Path
    inner = Σ-is-hlevel (S n) (ahl a₁ a₂) λ p → PathP-is-hlevel (bhl a₂)

×-is-hlevel : (n : Nat) → is-hlevel n A → is-hlevel n B → is-hlevel n (A × B)
×-is-hlevel n ahl bhl = Σ-is-hlevel n ahl (λ _ → bhl)

Lift-is-hlevel : ∀ {v} (n : Nat) → is-hlevel n A → is-hlevel n (Lift v A)
Lift-is-hlevel Z c .center = liftℓ (c .center)
Lift-is-hlevel Z c .paths (liftℓ a) i = liftℓ (c .paths a i)
Lift-is-hlevel (S Z) p (liftℓ a) (liftℓ b) i = liftℓ (p a b i)
Lift-is-hlevel {v = v} (S (S n)) hl (liftℓ a) (liftℓ b) =
  retract→is-hlevel (S n) fwd bwd (λ _ → refl) (Lift-is-hlevel (S n) (hl a b))
  where
    fwd : Lift v (a ≡ b) → liftℓ a ≡ liftℓ b
    fwd (liftℓ p) i = liftℓ (p i)

    bwd : liftℓ a ≡ liftℓ b → Lift v (a ≡ b)
    bwd q = liftℓ (λ i → q i .lower)

-- The Trunc trait record

record Trunc {ℓ} (T : Type ℓ) (n : Nat) : Type ℓ where
  no-eta-equality
  constructor trunc-instance
  field has-trunc : is-hlevel n T

open Trunc ⦃ ... ⦄ public
{-# INLINE Trunc.constructor #-}
{-# DISPLAY Trunc.has-trunc _ x = has-trunc x #-}

-- Entry points

trunc : (n : Nat) ⦃ _ : Trunc A n ⦄ → is-hlevel n A
trunc n = has-trunc

trunc! : ⦃ _ : Trunc A Z ⦄ → A
trunc! = has-trunc .center

prop! : ∀ {A : I → Type ℓ} ⦃ hl : ∀ {i} → Trunc (A i) (S Z) ⦄ {x : A i0} {y : A i1}
      → PathP A x y
prop! ⦃ hl ⦄ {x} {y} = is-prop→PathP (λ i → hl .has-trunc) x y

-- Instance helpers

basic-trunc : (n : Nat) → is-hlevel n A → ∀ {k} → Trunc A (n + k)
basic-trunc n hl {k} .has-trunc = is-hlevel-+ n k hl

prop-trunc : is-prop A → ∀ {k} → Trunc A (S k)
prop-trunc p {k} .has-trunc = is-prop→is-hlevel-suc {n = k} p

set-trunc : is-set A → ∀ {k} → Trunc A (S (S k))
set-trunc s {k} .has-trunc = is-hlevel-+ 2 k s

contr-trunc : is-contr A → ∀ {k} → Trunc A k
contr-trunc c {k} .has-trunc = is-contr→is-hlevel k c

-- Instances

instance
  Trunc-Π : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {n}
          → ⦃ ∀ {x} → Trunc (B x) n ⦄
          → Trunc ((x : A) → B x) n
  Trunc-Π {n = n} .has-trunc = Π-is-hlevel n (λ _ → trunc n)

  Trunc-Πi : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {n}
           → ⦃ hl : ∀ {x} → Trunc (B x) n ⦄
           → Trunc ({x : A} → B x) n
  Trunc-Πi {n = Z} ⦃ hl ⦄ .has-trunc .center {x} = hl .has-trunc .center
  Trunc-Πi {n = Z} ⦃ hl ⦄ .has-trunc .paths f i {x} = hl .has-trunc .paths f i
  Trunc-Πi {n = S Z} .has-trunc = Πi-is-prop (λ _ → trunc 1)
  Trunc-Πi {n = S (S n)} ⦃ hl ⦄ .has-trunc f g =
    retract→is-hlevel (S n) (λ p i {x} → p x i) (λ q x i → q i {x})
      (λ _ → refl) (Π-is-hlevel (S n) λ x → hl {x} .has-trunc (f {x}) (g {x}))

  Trunc-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {n}
          → ⦃ Trunc A n ⦄ → ⦃ ∀ {x} → Trunc (B x) n ⦄
          → Trunc (Σ B) n
  Trunc-Σ {n = n} .has-trunc = Σ-is-hlevel n (trunc n) (λ _ → trunc n)

  Trunc-× : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {n}
          → ⦃ Trunc A n ⦄ → ⦃ Trunc B n ⦄
          → Trunc (A × B) n
  Trunc-× {n = n} .has-trunc = ×-is-hlevel n (trunc n) (trunc n)

  Trunc-PathP : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} {n}
              → ⦃ Trunc (A i1) (S n) ⦄
              → Trunc (PathP A x y) n
  Trunc-PathP {n = n} .has-trunc = PathP-is-hlevel (trunc (S n))

  Trunc-Path : ∀ {ℓ} {A : Type ℓ} {x y : A} {n}
             → ⦃ Trunc A (S n) ⦄
             → Trunc (x ≡ y) n
  Trunc-Path {n = n} .has-trunc = Path-is-hlevel (trunc (S n))

  Trunc-Lift : ∀ {ℓ ℓ'} {A : Type ℓ} {n}
             → ⦃ Trunc A n ⦄
             → Trunc (Lift ℓ' A) n
  Trunc-Lift {n = n} .has-trunc = Lift-is-hlevel n (trunc n)

  Trunc-⊤ : ∀ {n} → Trunc ⊤ n
  Trunc-⊤ = contr-trunc (Contr tt (λ _ → refl))

  Trunc-Unit : ∀ {ℓ} {n} → Trunc (Unit {ℓ}) n
  Trunc-Unit = contr-trunc (Contr (liftℓ tt) (λ { (liftℓ tt) → refl }))

  Trunc-⊥ : ∀ {n} → Trunc ⊥ (S n)
  Trunc-⊥ = prop-trunc (λ x → ex-falso x)

  Trunc-is-prop : ∀ {ℓ} {A : Type ℓ} {n} → Trunc (is-prop A) (S n)
  Trunc-is-prop = prop-trunc (is-prop-is-prop _)

  Trunc-is-contr : ∀ {ℓ} {A : Type ℓ} {n} → Trunc (is-contr A) (S n)
  Trunc-is-contr = prop-trunc (is-contr-is-prop _)

  Trunc-is-hlevel : ∀ {ℓ} {A : Type ℓ} {n m} → Trunc (is-hlevel n A) (S m)
  Trunc-is-hlevel {n = n} = prop-trunc (is-hlevel-is-prop n)

{-# OVERLAPS Trunc-⊤ Trunc-Unit Trunc-⊥ #-}
{-# OVERLAPS Trunc-is-prop Trunc-is-contr Trunc-is-hlevel #-}
```
