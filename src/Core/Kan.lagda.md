Kan operations: homogeneous and heterogeneous composition and filling.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Kan where

open import Core.Type using (Level; Type; Exo; Exoω; _∘_)
open import Core.Base
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Sub

open import Agda.Builtin.Cubical.Path using (_≡_; PathP)

private module X where
  open import Agda.Primitive.Cubical public using (primTransp; primHComp)
open X public renaming (primTransp to transp) using () public

private
  variable
    ℓ : I → Level
    u : Level
    A : Type u
    U : I → Type u

```
Partial systems: the data for a composition problem.
```agda

Sys : (φ : I) → Type u → Exo u
Sys φ A = (i : I) → Partial (φ ∨ ~ i) A

PartialsP : (i : I) → ((i : I) → Type (ℓ i)) → Exoω
PartialsP φ A = (i : I) → Partial (φ ∨ ~ i) (A i)

sys-base : (φ : I) {A : Type u} → Sys φ A → A
sys-base _ u = u i0 1=1

sys-lid : {φ : I} {A : Type u} → Sys φ A → Partial φ A
sys-lid {φ} u (φ = i1) = u i1 1=1

SysExt : (φ : I) {A : Type u} → Sys φ A → Exo u
SysExt φ {A} u = A [ φ ↦ sys-lid u ]

```
Homogeneous composition (hcom) and filler (hfil). These will be very short
abbreviations to emphasize they are primitives.

```agda

hcom : (φ : I) → Sys φ A → A
hcom {A} φ u = X.primHComp sys (sys-base φ u)
  module hcom where
    sys : ∀ j → Partial φ A
    sys j (φ = i1) = u j 1=1
{-# DISPLAY X.primHComp {ℓ} {A} {φ} (hcom.sys _ u) _ = hcom {ℓ} {A} φ u #-}

hfil : (φ : I) → I → Sys φ A → A
hfil {A = A} φ i u = hcom (imp i φ) sys
  module hfil where
    sys : PartialsP (φ ∨ ~ i) (λ _ → A)
    sys j (i = i0) = u i0      1=1
    sys j (j = i0) = u i0      1=1
    sys j (φ = i1) = u (i ∧ j) 1=1
{-# DISPLAY hcom _ (hfil.sys φ i u) = hfil φ i u #-}

```
Named wrappers for the primitives.
```agda

sys-composite : {A : Type u} (φ : I) → Sys φ A → A
sys-composite = hcom

sys-filler : {A : Type u} (φ : I) (s : Sys φ A) (i : I) → A
sys-filler φ s i = hfil φ i s

sys-path : {A : Type u} (φ : I) (s : Sys φ A) → sys-base φ s ≡ sys-composite φ s
sys-path φ s i = sys-filler φ s i

module sys-filler where
  module _ {A : Type u} (φ : I) (s : Sys φ A) where
    pbase : sys-filler φ s i0 ≡ sys-base φ s
    pbase = λ _ → sys-base φ s

    plid : sys-filler φ s i1 ≡ sys-composite φ s
    plid = λ _ → sys-composite φ s

```
The space of system composites is contractible - this is the Kan condition.
```agda

SysComp : {A : Type u} (φ : I) (s : Sys φ A) → Type u
SysComp {A} φ s = Σ x ∶ A , sys-composite φ s ≡ x

SysComp-is-contr : {A : Type u} (φ : I) (s : Sys φ A) → is-contr (SysComp φ s)
SysComp-is-contr φ s .center = sys-composite φ s , sys-filler.plid φ s
SysComp-is-contr φ s .paths (x , p) i = p i , λ j → p (i ∧ j)

```
Heterogeneous composition (com) and filler (fil).

```agda

com : (A : (i : I) → Type (ℓ i)) (φ : I) → PartialsP φ A → A i1
com A φ u = X.primHComp sys (transp A i0 (u i0 1=1))
  module com where
  sys : ∀ _ → Partial φ (A i1)
  sys i (φ = i1) = transp (λ j → A (i ∨ j)) i (u i 1=1)
{-# DISPLAY X.primHComp {_} {_} {φ} (com.sys A _ u) _ = com A φ u #-}

fil : (A : ∀ i → Type (ℓ i)) → (φ : I) (i : I) (u : PartialsP φ A) → A i
fil A φ i u = com (∂.extend A i) (imp i φ) sys
  module fil where
    sys : PartialsP (imp i φ) (λ j → A (i ∧ j))
    sys j (i = i0) = u i0 1=1
    sys j (j = i0) = u i0 1=1
    sys j (φ = i1) = u (i ∧ j) 1=1
{-# DISPLAY com (∂.extend A i) _ (fil.sys A φ i u) = fil A φ i u #-}

```
Connection: degenerate square for monotone path extension.
```agda

hc : (A : ∀ i → Type (ℓ i))
   → (φ : I)
   → (f : (k : I) → A (~ k ∨ ~ φ))
   → (g : (k : I) → A (~ k ∨ φ))
   → f i0 ≡ g i0
   → A i1
hc A φ f g h = hcom (∂ φ) sys
  module hc where
    sys : PartialsP (∂ φ) (λ _ → A i1)
    sys i (φ = i0) = f i
    sys i (φ = i1) = g i
    sys i (i = i0) = h φ

    hc-fil : (i : I) → A i1
    hc-fil i = hfil (∂ φ) i sys
{-# DISPLAY hcom _ (hc.sys A φ f g p) = hc A φ f g p #-}
{-# DISPLAY hfil _ (hc.hc-fil A φ f g p i) = hc.hc-fil A φ f g p i #-}

kext : {A : ∀ i → Type (ℓ i)} (φ : I)
     → (P : ∀ i → A (φ ∧ i) → Type (ℓ (φ ∧ i)))
     → (g : ∀ i (a : A (φ ∧ i)) → P i a)
     → (f : ∀ k → A k)
     → P φ (f φ)
kext φ P g f = com (∂.cover φ P f) (∂ φ) sys
  module kext where
    sys : PartialsP (∂ φ) λ i → P (φ ∧ i) (f (φ ∧ i))
    sys k (φ = i0) = g i0 (f i0)
    sys k (k = i0) = g i0 (f i0)
    sys k (φ = i1) = g k (f k)
{-# DISPLAY com (∂.cover φ P f) φ (kext.sys φ P g f) = kext φ P g f #-}

HComposite : ∀ {u} {A : I → Type u} {w x : A i0} {y z : A i1}
            → (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) → Type u
HComposite {A} {w} {z} p q r = Σ s ∶ PathP A w z , HCell p q r s

module HComposite {u} {A : I → Type u} {w x : A i0} {y z : A i1}
  (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z)
  (α β : HComposite p q r)
  where
  path : α .fst ≡ β .fst
  path i j = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → α .snd j k
    k (i = i1) → β .snd j k
    k (j = i0) → p k
    k (j = i1) → r k
    k (k = i0) → q j

  coh : PathP (λ i → HCell p q r (path i)) (α .snd) (β .snd)
  coh i j k = hcom (∂ i ∨ ∂ j ∨ ~ k) λ where
    l (i = i0) → α .snd j (k ∧ l)
    l (i = i1) → β .snd j (k ∧ l)
    l (j = i0) → p (k ∧ l)
    l (j = i1) → r (k ∧ l)
    l (k = i0) → q j
    l (l = i0) → q j

  unique : α ≡ β
  unique i = path i , coh i

```

Triple Path Composition, which one might frame as a virtual double category.

```agda

module pcom {A : I → Type u} where
  module _  {w x : A i0} {y z : A i1} (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) where
    sys : (i : I) → Sys (∂ i) (A i)
    sys i k (i = i0) = p k
    sys i k (k = i0) = q i
    sys i k (i = i1) = r k

    composite : w ≡ z ∶ A
    composite i = hcom (∂ i) (sys i)

    fill : HCell p q r composite
    fill i j = hfil (∂ i) j (sys i)

    ctr : HComposite p q r
    ctr = composite , fill

    contr : is-contr (HComposite p q r)
    contr .center = composite , fill
    contr .paths f1 = HComposite.unique p q r (composite , fill) f1

    fibers : (pf : HComposite p q r) → ctr ≡ pf
    fibers = contr .paths

    unique : ((s , α) : HComposite p q r) → composite ≡ s
    unique = ap fst ∘ fibers

open pcom public using () renaming (composite to pcom; fill to pfil)
{-# DISPLAY hcom _ (pcom.sys p q r i) = pcom.composite p q r i #-}

module pfil {A : I → Type} where
  module _ {w x : A i0} {y z : A i1} (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) where
    coh : ((s , α) : HComposite p q r)
          → SquareP (λ i j → q j ≡ pcom.unique p q r (s , α) i j) (pcom.fill p q r) refl α refl
    coh = ap snd ∘ pcom.fibers p q r

  module _ {w x : A i0} {y z : A i1} (p : w ≡ x) (q : w ≡ y ∶ A) (r : y ≡ z) (s : x ≡ z ∶ A) where
    lcomp≡rcomp : HCell (sym p) s (sym r) q → pcom (sym p) s refl ≡ pcom refl q r
    lcomp≡rcomp α i j = hcom (∂ j ∨ ~ i) λ where
      k (j = i0) → p (~ i ∧ ~ k)
      k (i = i0) → pfil (sym p) s refl j k
      k (j = i1) → r (~ i ∨ k)
      k (k = i0) → α j i

  -- rwsk : ∀ {A : I → Type u} {x : A i0} {y z : A i1}
  --      → (p q : x ≡ y ∶ A) (r : y ≡ z) (s : x ≡ z ∶ A)
  --      → HCell refl p r s
  -- rwsk p α= {!!}

```

Ordinary Path Composition

```agda
module cat {A : I → Type u} {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z) where
  composite : x ≡ z ∶ A
  composite = pcom refl p q

  fill : HCell refl p q composite
  fill = pfil refl p q

  rfill : SquareP (λ i j → A (i ∨ ~ j)) (sym p) q refl composite
  rfill i j = hcom (∂ i ∨ ~ j) (s i j) where
    s : (i j : I) → Sys (∂ i ∨ ~ j) (A (i ∨ ~ j))
    s i j k (j = i0) = q (i ∧ k)
    s i j k (i = i0) = p (~ j)
    s i j k (k = i0) = p (i ∨ ~ j)
    s i j k (i = i1) = q k

  bfill : SquareP (λ i j → A (i ∨ j)) p composite refl q
  bfill i j = hcom (∂ i ∨ j) (s i j) where
    s : (i j : I) → Sys (∂ i ∨ j) (A (i ∨ j))
    s i j k (i = i0) = p j
    s i j k (i = i1) = q k
    s i j k (j = i1) = q (i ∧ k)
    s i j k (k = i0) = p (i ∨ j)


open cat public using () renaming (composite to infixr 9 _∙_)

```
## Groupoid Laws
```agda

module _ {A : Type u} where
  eqvr : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  eqvr p i j = cat.fill p refl j (~ i)

  eqvl : {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
  eqvl p i j = cat.rfill refl p j (~ i)

  invl : {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
  invl p i j = hcom (∂ j ∨ i) (λ k _ → p (~ j ∨ k))

  invr : {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
  invr p = invl (sym p)

  assoc : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
        → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  assoc p q r k = transpose (cat.fill p q) k ∙ transpose (cat.rfill q r) (~ k)

```
## Connection
```agda

conn : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) → HCell p p q q
conn {x} {y} {z} p q i j = hcom (∂ i ∨ ∂ j) sys
  module conn where
    sys : Sys (∂ i ∨ ∂ j) _
    sys k (k = i0) = q (i ∧ j)
    sys k (i = i0) = p (j ∨ ~ k)
    sys k (j = i0) = p (i ∨ ~ k)
    sys k (j = i1) = q i
    sys k (i = i1) = q j
{-# DISPLAY hcom _ (conn.sys p q i j) = conn p q i j #-}

```
## Triangles
```agda

Square : {A : Type u} {w x y z : A}
       → x ≡ w
       → x ≡ y
       → y ≡ z
       → w ≡ z
       → Type u
Square p q r s = PathP (∂.square _≡_ q s) p r

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
  pre i j = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ k)
    k (i = i1) → r j
    k (j = i0) → p (~ i ∧ k)
    k (j = i1) → q i
    k (k = i0) → sq j i
  {-# INLINE pre #-}

  post : Triangle (sym r) p (sym q)
  post i j = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → r (j ∨ k)
    k (i = i1) → p j
    k (j = i0) → r (~ i ∧ k)
    k (j = i1) → q (~ i)
    k (k = i0) → sq j (~ i)
  {-# INLINE post #-}

```

## Square operations

A path between paths gives a square with reflexivity on three sides.

```agda

-- Given p q : x ≡ y and α : p ≡ q, we get a square:
--       x ---refl---> x
--       |             |
--       p             q
--       |             |
--       v             v
--       y ---refl---> y
--
-- In Square notation: Square {w=y, x=x, y=x, z=y} p refl q refl
path→square
  : {A : Type u} {x y : A} {p q : x ≡ y}
  → p ≡ q → Square {w = y} {x = x} {y = x} {z = y} p refl q refl
path→square α i j = α i j
{-# INLINE path→square #-}

-- Note: Square and HCell are definitionally the same, just with different
-- argument conventions. The symmetry operations hflip and vflip are already
-- defined in Core.Base for HCell.

-- Square p q r s has:
--   p : x ≡ w  (left)
--   q : x ≡ y  (top)
--   r : y ≡ z  (right)
--   s : w ≡ z  (bottom)
--
-- Horizontal symmetry swaps left-right:
square-sym-h
  : {A : Type u} {w x y z : A}
    {p : x ≡ w} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
  → Square p q r s → Square r (sym q) p (sym s)
square-sym-h sq i j = sq (~ i) j
{-# INLINE square-sym-h #-}

-- Vertical symmetry swaps top-bottom:
square-sym-v
  : {A : Type u} {w x y z : A}
    {p : x ≡ w} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
  → Square p q r s → Square (sym p) s (sym r) q
square-sym-v sq i j = sq i (~ j)
{-# INLINE square-sym-v #-}

```
