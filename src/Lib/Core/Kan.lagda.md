```agda

{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Kan where

open import Lib.Core.Prim using (Level; Type; SSet; SSetω)
open import Lib.Core.Base

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
    U : I → Type u

Partials : (φ : I) → Type u → SSet u
Partials φ A = (i : I) → Partial (φ ∨ ~ i) A

PartialsP : (i : I) → ((i : I) → Type (ℓ i)) → SSetω
PartialsP φ A = (i : I) → Partial (φ ∨ ~ i) (A i)

hcomp : (φ : I) → Partials φ A → A
hcomp {A} φ u = X.primHComp sys (u i0 1=1)
  module hcomp where
    sys : ∀ j → Partial φ A
    sys j (φ = i1) = u j 1=1
{-# DISPLAY X.primHComp {ℓ} {A} {φ} (hcomp.sys _ u) _ = hcomp {ℓ} {A} φ u #-}

hfill : (φ : I) → I → Partials φ A → A
hfill {A = A} φ i u = hcomp (imp i φ) sys
  module hfill where
    sys : PartialsP (φ ∨ ~ i) (λ _ → A)
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
    sys : PartialsP (∂ φ) (λ _ → A i1)
    sys i (φ = i0) = f i
    sys i (φ = i1) = g i
    sys i (i = i0) = h φ

    fill : (i : I) → A i1
    fill i = hfill (∂ φ) i sys
{-# DISPLAY hcomp _ (hc.sys A φ f g p) = hc A φ f g p #-}
{-# DISPLAY hfill _ (hc.fill A φ f g p i) = hc.fill A φ f g p i #-}

module cat where
  private
    dsym : ∀ {u} {A : I → Type u} {x : A i0} {y : A i1} → PathP A x y → PathP (λ i → A (~ i)) y x
    dsym p i = p (~ i)

    idp : ∀ {u} {A : Type u} {x : A} → x ≡ x
    idp {x = x} _ = x

  module _ {A : I → Type u} {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z) where
    sys : (i : I) → Partials (∂ i) (A i)
    sys i k (i = i0) = x
    sys i k (k = i0) = p i
    sys i k (i = i1) = q k

    fun : x ≡ z ∶ A
    fun i = hcomp (∂ i) (sys i)

    fill : idp ≡ q ∶ ∂.square _≡_ p fun
    fill i j = hfill (∂ i) j (sys i)

  module _ {A : I → Type u} where
    cfill : {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (dsym p) idp q (fun p q)
    cfill {y} p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (j = i0) → y
      k (i = i0) → p (~ j)
      k (k = i0) → p (i ∨ ~ j)
      k (i = i1) → q (j ∧ k)

    bfill : {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ j)) p (fun p q) idp q
          -- p ≡ refl ∶ ∂.square _≡_ (p ∙ q) q
    bfill p q i j = hcomp (∂ i ∨ j) λ where
      k (i = i0) → p j
      k (i = i1) → q k
      k (j = i1) → q (i ∧ k)
      k (k = i0) → p (i ∨ j)

    rfill : {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (dsym p) q idp (fun p q)
          -- → dsym p ≡ erefl z ∶ ∂.square _≡_ q (p ∙ q)
    rfill {y} p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (j = i0) → q (i ∧ k)
      k (i = i0) → p (~ j)
      k (k = i0) → p (i ∨ ~ j)
      k (i = i1) → q k

  cone : {A : Type u} {x y z : A} (q : y ≡ z) (r : x ≡ z)
       → Square q (fun q (dsym r)) r (λ _ → z)
  cone q r i j = hcomp (∂ i ∨ j) λ where
    k (i = i0) → q (j ∧ k)
    k (i = i1) → r (j ∨ ~ k)
    k (j = i1) → q (i ∨ k)
    k (k = i0) → q i

  fan : {A : Type u} {x y z : A} (p : x ≡ y) (q : x ≡ z)
      → Square p (λ _ → x) q (fun (dsym p) q)
  fan {x} p q i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p j
    k (j = i0) → x
    k (i = i1) → q (j ∧ k)
    k (k = i0) → p (~ i ∧ j)

  lpush : {A : Type u} {w x y z : A}
        → (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
        → Square p q r s → Square (λ _ → x) q r (fun p s)
  lpush {x} p q r s sq i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → x
    k (j = i0) → q (i ∧ k)
    k (i = i1) → sq k j
    k (k = i0) → p (i ∧ j)

  rpush : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
        → Square p q r s → Square p (λ _ → x) (fun q r) s
  rpush {x} p q r s sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → x
    k (i = i0) → p (j ∧ k)
    k (j = i1) → sq i k
    k (k = i0) → q (i ∧ j)

  rpop : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
       → Square p (λ _ → x) (fun q r) s → Square p q r s
  rpop p q r s sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p j
    k (i = i1) → bfill q r j k
    k (j = i0) → q (i ∧ k)
    k (j = i1) → s i
    k (k = i0) → sq i j

  unitl : {x y : A} (p : x ≡ y) → fun refl p ≡ p
  unitl p i j = rfill refl p j (~ i)

  unitr : {x y : A} (p : x ≡ y) → fun p refl ≡ p
  unitr p i j = fill p refl j (~ i)

  invl : {x y : A} (p : x ≡ y) → fun (sym p) p ≡ refl
  invl {x} {y} p i j = hcomp (∂ j ∨ i) λ where
        k (j = i0) → y
        k (k = i0) → p (~ j)
        k (j = i1) → p k
        k (i = i1) → p (~ j ∨ k)

  invr : {x y : A} (p : x ≡ y) → fun p (sym p) ≡ refl
  invr p = invl (sym p)

  assoc : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
        → fun p (fun q r) ≡ fun (fun p q) r
  assoc {y} p q r k = fun (transpose (fill p q) k) (transpose (rfill q r) (~ k))

open cat using () renaming (fun to infixr 9 _∙_) public

{-# DISPLAY hcomp _ (cat.sys p q i) = (p ∙ q) i  #-}

comp : (A : (i : I) → Type (ℓ i)) (φ : I) → PartialsP φ A → A i1
comp A φ u = X.primHComp sys (transp A i0 (u i0 1=1))
  module comp where
  sys : ∀ _ → Partial φ (A i1)
  sys i (φ = i1) = transp (λ j → A (i ∨ j)) i (u i 1=1)
{-# DISPLAY X.primHComp {_} {_} {φ} (comp.sys A _ u) _ = comp A φ u #-}

fill : (A : ∀ i → Type (ℓ i)) → (φ : I) (i : I) (u : PartialsP φ A) → A i
fill A φ i u = comp (∂.extend A i) (imp i φ) sys
  module fill where
    sys : PartialsP (imp i φ) (λ j → A (i ∧ j))
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
    sys : PartialsP (∂ φ) λ i → P (φ ∧ i) (f (φ ∧ i))
    sys k (φ = i0) = g i0 (f i0)
    sys k (k = i0) = g i0 (f i0)
    sys k (φ = i1) = g k (f k)
{-# DISPLAY comp (∂.cover φ P f) φ (kext.sys φ P g f) = kext φ P g f #-}

hconn : {A : I → Type u} {x y : A i0} {z : A i1}
     → (p : x ≡ y) (q : y ≡ z ∶ A)
     → SquareP (λ i j → A (i ∧ j)) p p q q
hconn {A} {y} {z} p q i j = hcomp (∂ i ∨ ∂ j) sys
  module hconn where
    sys : Partials (∂ i ∨ ∂ j) (A (i ∧ j))
    sys k (k = i0) = q (i ∧ j)
    sys k (i = i0) = p (j ∨ ~ k)
    sys k (j = i0) = p (i ∨ ~ k)
    sys k (j = i1) = q i
    sys k (i = i1) = q j
{-# DISPLAY hcomp _ (hconn.sys p q i j) = hconn p q i j #-}

conn : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Square p p q q
conn = hconn

```
Squares involving three variables have a degenerate face, hence
they are triangles up to homotopy. We can read transformations of
these degenerate squares as transporting the refl term along one of
the paths, so from reflexivity at x to y, or y to z, and so on, so
we define "pre" and "post" operations to implement this.
```

Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  → Type ℓ
Triangle p q r = Square refl p q r

module Triangle {ℓ} {A : Type ℓ} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  (sq : Triangle p q r)
  where
  pre : Triangle (sym p) r q
  pre i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ k)
    k (i = i1) → r j
    k (j = i0) → p (~ i ∧ k)
    k (j = i1) → q i
    k (k = i0) → sq j i
  {-# INLINE pre #-}

  post : Triangle (sym r) p (sym q)
  post i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → r (j ∨ k)
    k (i = i1) → p j
    k (j = i0) → r (~ i ∧ k)
    k (j = i1) → q (~ i)
    k (k = i0) → sq j (~ i)
  {-# INLINE post #-}

begin_ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ p = p

_≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = sym p ∙ q

_∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
x ∎ = refl

infix  1 begin_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
infix  3 _∎
