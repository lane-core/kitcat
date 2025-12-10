```agda

{-# OPTIONS --safe --erased-cubical #-}

module Lib.Cubical.Kan where

open import Lib.Type using (Level; Type; SSet; SSetω)
open import Lib.Cubical.Base

open import Agda.Builtin.Cubical.Path using (_≡_; PathP)

private module X where
  open import Agda.Primitive.Cubical public using (primTransp; primHComp)
open X public renaming (primTransp to transp) using () public
-- primHComp  : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A

private
  variable
    ℓ : I → Level
    u : Level
    A : Type u

module _ (A : ∀ i → Type (ℓ i)) where
  coe0i : (i : I) → A i0 → A i
  coe0i i = transp (∂.extend A i) (~ i)
  {-# INLINE coe0i #-}

  coe01 : A i0 → A i1
  coe01 = transp A i0
  {-# INLINE coe01 #-}

  coe10 : A i1 → A i0
  coe10 = transp (∂.sym A) i0
  {-# INLINE coe10 #-}

  coei1 : (i : I) → A i → A i1
  coei1 i = transp (∂.contract A i) i
  {-# INLINE coei1 #-}

  coei0 : (i : I) → A i → A i0
  coei0 i a = transp (∂.sym (∂.extend A i)) (~ i) a
  {-# INLINE coei0 #-}

  coe1i : (i : I) → A i1 → A i
  coe1i i = transp (∂.sym (∂.contract A i)) i
  {-# INLINE coe1i #-}

  coe : (i j : I) → A i → A j
  coe i j = transp (λ k → A (ierp k i j)) (ieq i j)
  {-# INLINE coe #-}

  transport-syntax = coe01
  syntax transport-syntax (λ i → b) = ∂ i => b

{-# DISPLAY transp A i0 = coe01 A #-}
{-# DISPLAY transp (∂.extend A i) _ = coe0i A i #-}
{-# DISPLAY transp (∂.contract A i) _ = coei1 A i #-}
{-# DISPLAY transp (∂.sym A) i0 = coe10 A #-}
{-# DISPLAY transp (∂.sym (∂.contract A i)) _ = coe1i A i #-}
{-# DISPLAY transport-syntax = coe01 #-}

Partials : (i : I) → ((i : I) → Type (ℓ i)) → SSetω
Partials φ A = (i : I) → Partial (φ ∨ ~ i) (A i)

hcomp : (φ : I) → Partials φ (λ _ → A) → A
hcomp {A} φ u = X.primHComp sys (u i0 1=1)
  module hcomp where
    sys : ∀ j → Partial φ A
    sys j (φ = i1) = u j 1=1
{-# DISPLAY X.primHComp {ℓ} {A} {φ} (hcomp.sys _ u) _ = hcomp {ℓ} {A} φ u #-}

comp : (A : (i : I) → Type (ℓ i)) (φ : I) → Partials φ A → A i1
comp A φ u = X.primHComp sys (transp A i0 (u i0 1=1))
  module comp where
  sys : ∀ _ → Partial φ (A i1)
  sys i (φ = i1) = transp (λ j → A (i ∨ j)) i (u i 1=1)
{-# DISPLAY X.primHComp {_} {_} {φ} (comp.sys A _ u) _ = comp A φ u #-}

hfill : (φ : I) → I → Partials φ (λ _ → A) → A
hfill {A = A} φ i u = hcomp (imp i φ) sys
  module hfill where
    sys : Partials (φ ∨ ~ i) (λ _ → A)
    sys j (i = i0) = u i0      1=1
    sys j (j = i0) = u i0      1=1
    sys j (φ = i1) = u (i ∧ j) 1=1
{-# DISPLAY hcomp _ (hfill.sys φ i u) = hfill φ i u #-}

hc : (A : ∀ i → Type (ℓ i))
   → (φ : I)
   → (f : (k : I) → A (~ k ∨ ~ φ))
   → (g : (k : I) → A (~ k ∨ φ))
   → f i0 ≡ g i0
   → A i1
hc A φ f g h = hcomp (∂ φ) sys
  module hc where
    sys : Partials (∂ φ) (λ _ → A i1)
    sys i (φ = i0) = f i
    sys i (φ = i1) = g i
    sys i (i = i0) = h φ

    fill : (i : I) → A i1
    fill i = hfill (∂ φ) i sys
{-# DISPLAY hcomp _ (hc.sys A φ f g p) = hc A φ f g p #-}
{-# DISPLAY hfill _ (hc.fill A φ f g p i) = hc.fill A φ f g p i #-}

fill : (A : ∀ i → Type (ℓ i)) → (φ : I) (i : I) (u : Partials φ A) → A i
fill A φ i u = comp (∂.extend A i) (imp i φ) sys
  module fill where
    sys : Partials (imp i φ) (λ j → A (i ∧ j))
    sys j (i = i0) = u i0 1=1
    sys j (j = i0) = u i0 1=1
    sys j (φ = i1) = u (i ∧ j) 1=1
{-# DISPLAY comp (∂.extend A i) _ (hc.sys A φ i u) = fill A φ i u #-}

kext : {A : ∀ i → Type (ℓ i)} (φ : I)
     → (P : ∀ i → A (φ ∧ i) → Type (ℓ (φ ∧ i)))
     → (g : ∀ i (a : A (φ ∧ i)) → P i a)
     → (f : ∀ k → A k)
     → P φ (f φ)
kext φ P g f = comp (∂.cover φ P f) (∂ φ) sys
  module kext where
    sys : Partials (∂ φ) λ i → P (φ ∧ i) (f (φ ∧ i))
    sys k (φ = i0) = g i0 (f i0)
    sys k (k = i0) = g i0 (f i0)
    sys k (φ = i1) = g k (f k)
{-# DISPLAY comp (∂.cover φ P f) φ (kext.sys φ P g f) = kext φ P g f #-}

transport-filler : (A : I → Type u) (x : A i0) → PathP A x (coe01 A x)
transport-filler A x i = coe0i A i x

module transp (A : I → Type u) where
  fill10 : (x : A i1) → PathP (λ i → A (~ i)) x (coe10 A x)
  fill10 x j = coe1i A (~ j) x

  fill0i : (x : A i0) (i : I) → PathP (λ j → A (i ∧ j)) x (coe0i A i x)
  fill0i x i j = coe0i A (i ∧ j) x

  fill1i : (x : A i1) (i : I) → PathP (λ j → A (i ∨ ~ j)) x (coe1i A i x)
  fill1i x i j = coe1i A (i ∨ ~ j) x

  filli : ∀ i x → coe A i i x ≡ x
  filli i x j = transp (λ _ → A i) (j ∨ i ∨ ~ i) x

  path : ∀ {ℓ} (A : I → Type ℓ) (p : ∀ i → A i) i j → coe A i j (p i) ≡ p j
  path A p i j k = transp
    (λ l → A (ierp k (ierp l i j) j))
    (ierp k (ieq i j) i1)
    (p (ierp k i j))

Path-over : ∀ {u} (A : I → Type u) → A i0 → A i1 → Type u
Path-over A x y = coe01 A x ≡ y

module Path-over {u} {A : I → Type u} {x} {y} where
  to-pathp : Path-over A x y → PathP A x y
  to-pathp p i = hcomp (∂ i) λ where
    j (i = i0) → x
    j (i = i1) → p j
    j (j = i0) → coe0i A i x

  from-pathp : PathP A x y → Path-over A x y
  from-pathp p i = coei1 A i (p i)

  eq-PathP : ∀ {ℓ} (P : I → Type ℓ) x y → PathP P x y ≡ Path-over P x y
  eq-PathP P x y i = PathP (∂.contract P i) (transport-filler P x i) y

