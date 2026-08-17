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

HSys : (i : I) → ((i : I) → Type (ℓ i)) → Exoω
HSys φ A = (i : I) → Partial (φ ∨ ~ i) (A i)

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

## Contractibility and Extension

No reason to change what 1lab did for the following two lemmas:

```agda

is-contr→extend : ∀ {ℓ} {A : Type ℓ} → is-contr A
                → (i : I) (p : Partial i A) →  A [ i ↦ p ]
is-contr→extend c i p = inS do
  hcom (∂ i) λ where
      j (i = i1) → c .paths (p 1=1) j
      j (i = i0) → c .center
      j (j = i0) → c .center
{-# INLINE is-contr→extend #-}

extend→is-contr : ∀ {u} {A : Type u}
                → (∀ i (p : Partial i A) → A [ i ↦ p ])
                → is-contr A
extend→is-contr ex .center = outS do ex i0 λ ()
extend→is-contr ex .paths x i = outS do ex i (λ _ → x)

is-contr→is-prop : ∀ {u} {A : Type u} → is-contr A → is-prop A
is-contr→is-prop c x y i = outS do
  is-contr→extend c (∂ i) λ where
    (i = i0) → x
    (i = i1) → y

is-contr→is-set : ∀ {u} {A : Type u} → is-contr A → is-set A
is-contr→is-set c x y p q i j = outS do
  is-contr→extend c (∂ i ∨ ∂ j) λ where
    (i = i0) → p j
    (i = i1) → q j
    (j = i0) → x
    (j = i1) → y

total-contr-unique
  : ∀ {u v} {X : Type u} {P : X → Type v}
  → is-contr (Σ P)
  → {a b : X} {α : P a} {β : P b}
  → (p q : a ≡ b)
  → PathP (λ i → P (p i)) α β
  → PathP (λ i → P (q i)) α β
  → p ≡ q
total-contr-unique cc {α} {β} p q αp αq =
  ap (ap fst)
    (is-contr→is-set cc (_ , α) (_ , β)
      (λ i → p i , αp i) (λ i → q i , αq i))

Σ-contr-contr
  : ∀ {u v} {A : Type u} {B : A → Type v}
  → is-contr A → ((a : A) → is-contr (B a)) → is-contr (Σ B)
Σ-contr-contr cA cB .center = cA .center , cB (cA .center) .center
Σ-contr-contr cA cB .paths (a , b) i = cA .paths a i , outS do
  is-contr→extend (cB (cA .paths a i)) (∂ i) λ where
    (i = i0) → cB (cA .center) .center
    (i = i1) → b

TotalP
  : ∀ {u v} {A : Type u} {B : A → Type v} {x} (a : B x)
  → is-contr (Σ y ∶ A , Σ q ∶ (x ≡ y) , Σ b ∶ B y , PathP (λ i → B (q i)) a b)
TotalP {x} a .center = x , refl , a , refl
TotalP a .paths (y , q , b , α) i =
  q i , (λ j → q (i ∧ j)) , α i , λ j → α (i ∧ j)

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

Total-sys : {A : Type u} (φ : I) (s : Sys φ A) → Type u
Total-sys {A} φ s = Σ (λ (x : A) → sys-composite φ s ≡ x)

Total-sys-contr : {A : Type u} (φ : I) (s : Sys φ A) → is-contr (Total-sys φ s)
Total-sys-contr φ s .center = sys-composite φ s , sys-filler.plid φ s
Total-sys-contr φ s .paths (x , p) i = p i , λ j → p (i ∧ j)

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

kext : {w : Level} {A : ∀ i → Type (ℓ i)} (φ : I)
     → (P : ∀ i → A (φ ∧ i) → Type w)
     → (g : ∀ i (a : A (φ ∧ i)) → P i a)
     → (f : ∀ k → A k)
     → P φ (f φ)
kext {w = w} φ P g f = com (∂.cover (λ _ → w) φ P f) (∂ φ) sys
  module kext where
    sys : PartialsP (∂ φ) λ i → P (φ ∧ i) (f (φ ∧ i))
    sys k (φ = i0) = g i0 (f i0)
    sys k (k = i0) = g i0 (f i0)
    sys k (φ = i1) = g k (f k)
{-# DISPLAY com (∂.cover _ φ P f) φ (kext.sys φ P g f) = kext φ P g f #-}

HComposite : ∀ {u} {A : I → Type u} {w x : A i0} {y z : A i1}
            → (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) → Type u
HComposite {A} {w} {z} p q r = Σ (λ (s : PathP A w z) → HCell p q r s)

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

module pcom where
  module base {A : I → Type u} {w x : A i0} {y z : A i1}
    (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z)
    where
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
    contr .paths = HComposite.unique p q r (composite , fill)

    fibers : (pf : HComposite p q r) → ctr ≡ pf
    fibers = contr .paths

    unique : ((s , α) : HComposite p q r) → composite ≡ s
    unique = ap fst ∘ fibers

  open base public

  module _ {A : I → Type u} {x : A i0} {y : A i1}
    (q : x ≡ y ∶ A) where
    unit : composite refl q refl ≡ q
    unit = unique refl q refl (q , λ i _ → q i)

  module _ {A : Type u} {x y : A} (q : x ≡ y) where
    ideml : composite refl refl q ≡ q
    ideml = unique refl refl q (q , (λ i j → q (i ∧ j)))

    idemr : composite (sym q) refl refl ≡ q
    idemr = unique (sym q) refl refl (q , λ i j → q (i ∨ ~ j))

  module _ {A : I → Type u} {v : Level} {B : I → Type v}
    (f : ∀ i → A i → B i)
    {w x : A i0} {y z : A i1}
    (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) where
    private module P = base {A = B}
    map : (λ i → f i (composite p q r i))
        ≡ P.composite (λ j → f i0 (p j)) (λ i → f i (q i)) (λ j → f i1 (r j))
    map = sym (P.unique
                ( λ j → f i0 (p j)) (λ i → f i (q i)) (λ j → f i1 (r j) )
                ( (λ i → f i (composite p q r i) )
                , λ i j → f i (fill p q r i j)) )

  module _ {A : Type u} where
    private
      inv-sides-filler
        : {x y z : A} (p : x ≡ y) (q : x ≡ z)
        → Square p q (sym q) (sym p)
      inv-sides-filler {x = x} p q i j =
        hcom (∂ i ∨ ∂ j) λ where
          k (i = i0) → p (k ∧ j)
          k (i = i1) → q (~ j ∧ k)
          k (j = i0) → q (i ∧ k)
          k (j = i1) → p (~ i ∧ k)
          k (k = i0) → x

    lr
      : {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → composite refl p q ≡ composite (sym p) q refl
    lr p q i j =
      hcom (∂ j) λ where
        k (j = i0) → p (i ∧ (~ k))
        k (j = i1) → q (k ∨ i)
        k (k = i0) → inv-sides-filler q (sym p) (~ i) j

    lsplit
      : {w x y z : A} (p : w ≡ x) (q : x ≡ y)
        (r : y ≡ z)
      → composite (sym p) q r
      ≡ composite refl (composite (sym p) q refl) r
    lsplit p q r j i =
      hcom (∂ i) λ where
        k (i = i0) → p (~ j ∧ ~ k)
        k (i = i1) → r k
        k (k = i0) → fill (sym p) q refl i j

    rsplit
      : {w x y z : A} (p : w ≡ x) (q : x ≡ y)
        (r : y ≡ z)
      → composite (sym p) q r
      ≡ composite (sym p) (composite refl q r) refl
    rsplit p q r j i =
      hcom (∂ i) λ where
        k (i = i0) → p (~ k)
        k (i = i1) → r (j ∨ k)
        k (k = i0) → fill refl q r i j

    catr
      : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
      → composite (sym p) q r ≡ composite refl (composite refl p q) r
    catr p q r =
      composite refl (lsplit p q r)
        (λ i → composite refl (lr p q (~ i)) r)

    catl
      : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
      → composite (sym p) q r ≡ composite refl p (composite refl q r)
    catl p q r =
      composite refl (rsplit p q r)
        (sym (lr p (composite refl q r)))

    private
      invl-filler
        : {x y : A} (p : x ≡ y)
        → I → I → I → A
      invl-filler p i j k =
        hfil (i ∨ ∂ j) k λ where
          l (i = i1) → p l
          l (j = i0) → p l
          l (j = i1) → p l
          l (l = i0) → p i0

    invl
      : {x y : A} (p : x ≡ y)
      → composite p refl p ≡ refl
    invl p i j = invl-filler p i j i1

  -- pcom-coe interaction: how ternary composition interacts
  -- with transport between fibers of a type family.

  module _ {A : I → Type u} where

    private
      -- Local abbreviations for transport along A and ∂.sym A
      coe-A : (i : I) → A i0 → A i
      coe-A i = transp (∂.extend A i) (~ i)

      coe-A⁻ : (i : I) → A i1 → A (~ i)
      coe-A⁻ i = transp (∂.extend (∂.sym A) i) (~ i)

      coe-filler-A : (x : A i0) → PathP A x (coe-A i1 x)
      coe-filler-A x i = coe-A i x

    -- coe-fill: the round-trip through coe-filler.
    -- pcom (sym a) (coe-filler x) refl gives PathP A w (coe01 A x).
    -- Transporting back via com (∂.sym A) recovers a : w ≡ x.
    -- coe-fill
    --   : {w x : A i0} (a : w ≡ x)
    --   → (j : I) → com (∂.sym A) (∂ j) (λ where
    --       k (j = i0) → composite (sym a) (coe-filler-A x) refl (~ k)
    --       k (k = i0) → coe-A i1 x
    --       k (j = i1) → coe-A (~ k) x)
    --     ≡ a j
    -- -- The i=0 face must match inv (emb a) j, whose j=i0 face
    -- -- is pcom (sym a) (coe-filler-A x) refl (~ k).
    -- -- The i=1 face needs coe-A (~ k) (a j).
    -- -- These differ at (j=i0): pcom involves coe-filler-A x
    -- -- while coe involves a (~ i). The interpolation between
    -- -- them requires composing in A (~ k) at each k.
    -- coe-fill {w} {x} a j = {!!}

    -- het: pcom already handles heterogeneous center argument.
    -- This just documents that composite p q r : PathP A w z
    -- when p : x ≡ w in A i0, q : PathP A x y, r : y ≡ z in A i1.
    het
      : {w x : A i0} {y z : A i1}
        (p : x ≡ w) (q : PathP A x y) (r : y ≡ z)
      → PathP A w z
    het p q r = composite p q r

open pcom public using () renaming (composite to pcom; fill to pfil)
{-# DISPLAY hcom _ (pcom.sys p q r i) = pcom.composite p q r i #-}

contr-face
  : ∀ {u v} {X : Type u} {P : X → Type v}
  → (c : is-contr (Σ P))
  → {a b : X} {α α' : P a} {β β' : P b}
  → (σ : (a , α) ≡ (b , β))
  → (w : α ≡ α')
    (core : (a , α') ≡ (b , β'))
    (v : β' ≡ β)
  → ap fst σ ≡ ap fst core
contr-face c {a} {b} σ w core v =
  pcom (sym (total-contr-unique c
    (ap fst σ) (ap fst tri)
    (ap snd σ) (ap snd tri)))
  (pcom.map (λ _ → fst) (sym w') core v')
  (pcom.unit (ap fst core))
  where
    w' : (a , _) ≡ (a , _)
    w' i = a , w i
    v' : (b , _) ≡ (b , _)
    v' i = b , v i
    tri = pcom (sym w') core v'

module pfil {A : I → Type} where
  module _ {w x : A i0} {y z : A i1} (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) where
    coh
      : ((s , α) : HComposite p q r)
      → SquareP (λ i j → q j ≡ pcom.unique p q r (s , α) i j) (pcom.fill p q r) refl α refl
    coh = ap snd ∘ pcom.fibers p q r

  module _ {w x : A i0} {y z : A i1} (p : w ≡ x) (q : w ≡ y ∶ A) (r : y ≡ z) (s : x ≡ z ∶ A) where
    lcomp≡rcomp
      : HCell (sym p) s (sym r) q
      → pcom (sym p) s refl ≡ pcom refl q r
    lcomp≡rcomp α i j = hcom (∂ j ∨ ~ i) λ where
      k (j = i0) → p (~ i ∧ ~ k)
      k (i = i0) → pfil (sym p) s refl j k
      k (j = i1) → r (~ i ∨ k)
      k (k = i0) → α j i


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

## Composition uniqueness

Any two fillers for the same system agree on their lids.

```agda

hcom-unique
  : ∀ {u} {A : Type u} {φ : I}
  → (u : Sys φ A)
  → (h2 : ∀ i → A [ (φ ∨ ~ i) ↦
      (λ { (φ = i1) → u i 1=1; (i = i0) → sys-base φ u }) ])
  → (hcom φ u ≡ outS (h2 i1))
    [ φ ↦ (λ { (φ = i1) → (λ _ → u i1 1=1) }) ]
hcom-unique {φ = φ} u h2 = inS λ i →
  hcom (φ ∨ i) λ where
    k (φ = i1) → u k 1=1
    k (i = i1) → outS (h2 k)
    k (k = i0) → sys-base φ u

hcom-lid-unique
  : ∀ {u} {A : Type u} {φ : I}
  → (u : Sys φ A)
  → (h1 h2 : ∀ i → A [ (φ ∨ ~ i) ↦
      (λ { (φ = i1) → u i 1=1; (i = i0) → sys-base φ u }) ])
  → (outS (h1 i1) ≡ outS (h2 i1))
    [ φ ↦ (λ { (φ = i1) → (λ _ → u i1 1=1) }) ]
hcom-lid-unique {φ = φ} u h1 h2 = inS λ i →
  hcom (φ ∨ ∂ i) λ where
    k (φ = i1) → u k 1=1
    k (i = i0) → outS (h1 k)
    k (i = i1) → outS (h2 k)
    k (k = i0) → sys-base φ u

com-unique
  : ∀ {u} {A : I → Type u} {φ : I}
  → (u : PartialsP φ A)
  → (h2 : ∀ i → A i [ (φ ∨ ~ i) ↦
      (λ { (φ = i1) → u i 1=1; (i = i0) → u i0 1=1 }) ])
  → (com A φ u ≡ outS (h2 i1))
    [ φ ↦ (λ { (φ = i1) → (λ _ → u i1 1=1) }) ]
com-unique {A = A} {φ = φ} u h2 = inS λ i →
  com A (φ ∨ i) λ where
    k (φ = i1) → u k 1=1
    k (i = i1) → outS (h2 k)
    k (k = i0) → u i0 1=1

com-lid-unique
  : ∀ {u} {A : I → Type u} {φ : I}
  → (u : PartialsP φ A)
  → (h1 h2 : ∀ i → A i [ (φ ∨ ~ i) ↦
      (λ { (φ = i1) → u i 1=1; (i = i0) → u i0 1=1 }) ])
  → (outS (h1 i1) ≡ outS (h2 i1))
    [ φ ↦ (λ { (φ = i1) → (λ _ → u i1 1=1) }) ]
com-lid-unique {A = A} {φ = φ} u h1 h2 = inS λ i →
  com A (φ ∨ ∂ i) λ where
    k (φ = i1) → u k 1=1
    k (i = i0) → outS (h1 k)
    k (i = i1) → outS (h2 k)
    k (k = i0) → u i0 1=1

hcom-cong
  : ∀ {u} {A : Type u} {φ : I}
  → (u : Sys φ A) (u' : Sys φ A)
  → (ueq : ∀ i → PartialP (φ ∨ ~ i)
      (λ o → u i o ≡ u' i o))
  → (hcom φ u ≡ hcom φ u')
    [ φ ↦ (λ { (φ = i1) → ueq i1 1=1 }) ]
hcom-cong {φ = φ} u u' ueq = inS λ j →
  hcom φ λ where
    i (φ = i1) → ueq i 1=1 j
    i (i = i0) → ueq i0 1=1 j

```

Ordinary Path Composition

```agda
module cat where


  module _  {A : I → Type u} {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z) where

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

  private
    _∙_ = composite; infixr 9 _∙_

  module _ {A : Type u} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) where
    lcoh : Square (sym p) q r (p ∙ q ∙ r)
    lcoh i j = hcom (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ j)
      k (i = i1) → fill q r k j
      k (j = i0) → q (i ∧ k)
      k (k = i0) → p (i ∨ ~ j)

    rcoh : Square (sym p) q r ((p ∙ q) ∙ r)
    rcoh i j = hcom (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ j)
      k (i = i1) → r (j ∧ k)
      k (j = i0) → q i
      k (k = i0) → rfill p q i j

open cat public using () renaming (composite to infixr 9 _∙_)

-- comp-pathp concatenates two PathPs over composable type paths:
-- the two-family image of the ternary composition, glued along
-- the cat.fill filler of the type-path composite.
comp-pathp
  : ∀ {u} {X Y Z : Type u} {x : X} {y : Y} {z : Z}
  → (A : X ≡ Y) (B : Y ≡ Z)
  → PathP (λ i → A i) x y → PathP (λ i → B i) y z
  → PathP (λ i → (A ∙ B) i) x z
comp-pathp A B P Q i =
  com (λ j → cat.fill A B i j) (∂ i) λ where
    j (i = i0) → P i0
    j (i = i1) → Q j
    j (j = i0) → P i

-- comp-pathp₁: the one-base-path version, for a unary family —
-- the line is F of a single object path, glued along the
-- cat.fill filler of the base composite
comp-pathp₁
  : ∀ {u w} {X : Type u} (F : X → Type w)
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {h₀ : F a₀} {h₁ : F a₁} {h₂ : F a₂}
  → PathP (λ i → F (pa i)) h₀ h₁
  → PathP (λ i → F (qa i)) h₁ h₂
  → PathP (λ i → F ((pa ∙ qa) i)) h₀ h₂
comp-pathp₁ F pa qa {h₀ = h₀} P Q i =
  com (λ j → F (cat.fill pa qa i j)) (∂ i) λ where
    j (i = i0) → h₀
    j (i = i1) → Q j
    j (j = i0) → P i

-- comp-pathp₁-fill: the filler of comp-pathp₁ — the same com taken
-- as a fil, sliding the line from P at m = i0 to the composite at
-- m = i1 along the cat.fill filler of the base composite. Both
-- ends are definitional (the fil cap and the com), so a
-- construction applied along the filler is a strict-endpoint square.
comp-pathp₁-fill
  : ∀ {u w} {X : Type u} (F : X → Type w)
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {h₀ : F a₀} {h₁ : F a₁} {h₂ : F a₂}
    (P : PathP (λ i → F (pa i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i)) h₁ h₂)
    (m : I)
  → PathP (λ i → F (cat.fill pa qa i m)) h₀ (Q m)
comp-pathp₁-fill F pa qa {h₀ = h₀} P Q m i =
  fil (λ j → F (cat.fill pa qa i j)) (∂ i) m λ where
    j (i = i0) → h₀
    j (i = i1) → Q j
    j (j = i0) → P i

-- comp-pathp₁-over: a section over comp-pathp₁ — the unary sibling
-- of comp-pathp₂-over, glued over the com filler of comp-pathp₁
-- itself, whose lid at j = i1 is comp-pathp₁ definitionally
comp-pathp₁-over
  : ∀ {u w w'} {X : Type u}
    (F : X → Type w) (G : ∀ x → F x → Type w')
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {h₀ : F a₀} {h₁ : F a₁} {h₂ : F a₂}
    (P : PathP (λ i → F (pa i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i)) h₁ h₂)
    {g₀ : G a₀ h₀} {g₁ : G a₁ h₁} {g₂ : G a₂ h₂}
  → PathP (λ i → G (pa i) (P i)) g₀ g₁
  → PathP (λ i → G (qa i) (Q i)) g₁ g₂
  → PathP (λ i → G ((pa ∙ qa) i) (comp-pathp₁ F pa qa P Q i)) g₀ g₂
comp-pathp₁-over F G pa qa {h₀ = h₀} P Q {g₀ = g₀} P' Q' i =
  com (λ j → G (cat.fill pa qa i j) (base j)) (∂ i) λ where
    j (i = i0) → g₀
    j (i = i1) → Q' j
    j (j = i0) → P' i
  where
    base : (j : I) → F (cat.fill pa qa i j)
    base j =
      fil (λ j → F (cat.fill pa qa i j)) (∂ i) j λ where
        j (i = i0) → h₀
        j (i = i1) → Q j
        j (j = i0) → P i

-- comp-pathp₂: the two-base-path version, for a binary family —
-- the line is F of two object paths, so the filler is taken
-- pointwise along the cat.fill fillers of the two base composites
comp-pathp₂
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {b₀ b₁ b₂ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂}
  → PathP (λ i → F (pa i) (pb i)) h₀ h₁
  → PathP (λ i → F (qa i) (qb i)) h₁ h₂
  → PathP (λ i → F ((pa ∙ qa) i) ((pb ∙ qb) i)) h₀ h₂
comp-pathp₂ F pa qa pb qb {h₀ = h₀} P Q i =
  com (λ j → F (cat.fill pa qa i j) (cat.fill pb qb i j)) (∂ i) λ where
    j (i = i0) → h₀
    j (i = i1) → Q j
    j (j = i0) → P i

-- comp-pathp₂-fill: the filler of comp-pathp₂ — the same com taken
-- as a fil, sliding the line from P at m = i0 to the composite at
-- m = i1 along the cat.fill fillers of the two base composites.
-- Both ends are definitional (the fil cap and the com), so a
-- construction applied along the filler is a strict-endpoint square.
comp-pathp₂-fill
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {b₀ b₁ b₂ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i) (qb i)) h₁ h₂)
    (m : I)
  → PathP (λ i → F (cat.fill pa qa i m) (cat.fill pb qb i m)) h₀ (Q m)
comp-pathp₂-fill F pa qa pb qb {h₀ = h₀} P Q m i =
  fil (λ j → F (cat.fill pa qa i j) (cat.fill pb qb i j)) (∂ i) m λ where
    j (i = i0) → h₀
    j (i = i1) → Q j
    j (j = i0) → P i

-- comp-pathp₂-over: a section over comp-pathp₂ — lines of
-- G-elements over the two glued F-lines glue over the com filler
-- of comp-pathp₂ itself, whose lid at j = i1 is comp-pathp₂
-- definitionally. hcomp at a Σ-type does not project
-- componentwise, so a Σ-valued gluing whose fst is the fst-level
-- comp-pathp₂ must be assembled from this pair, not projected.
comp-pathp₂-over
  : ∀ {u v w w'} {X : Type u} {Y : Type v}
    (F : X → Y → Type w) (G : ∀ x y → F x y → Type w')
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {b₀ b₁ b₂ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i) (qb i)) h₁ h₂)
    {g₀ : G a₀ b₀ h₀} {g₁ : G a₁ b₁ h₁} {g₂ : G a₂ b₂ h₂}
  → PathP (λ i → G (pa i) (pb i) (P i)) g₀ g₁
  → PathP (λ i → G (qa i) (qb i) (Q i)) g₁ g₂
  → PathP (λ i → G ((pa ∙ qa) i) ((pb ∙ qb) i)
                   (comp-pathp₂ F pa qa pb qb P Q i))
          g₀ g₂
comp-pathp₂-over F G pa qa pb qb {h₀ = h₀} P Q {g₀ = g₀} P' Q' i =
  com (λ j → G (cat.fill pa qa i j) (cat.fill pb qb i j) (base j))
      (∂ i) λ where
    j (i = i0) → g₀
    j (i = i1) → Q' j
    j (j = i0) → P' i
  where
    base : (j : I) → F (cat.fill pa qa i j) (cat.fill pb qb i j)
    base j =
      fil (λ j → F (cat.fill pa qa i j) (cat.fill pb qb i j)) (∂ i) j λ where
        j (i = i0) → h₀
        j (i = i1) → Q j
        j (j = i0) → P i

-- pathp-ends: two PathPs over one line whose i0-ends are
-- identified have identified i1-ends — the com over the shared
-- family, walls the two lines, base the identification. The
-- workhorse for comparing a whiskered filler line against a
-- stated diagonal without eliminating either base path.
pathp-ends
  : ∀ {u} {A : I → Type u}
    {a₀ b₀ : A i0} {a₁ b₁ : A i1}
  → PathP A a₀ a₁ → PathP A b₀ b₁
  → a₀ ≡ b₀ → a₁ ≡ b₁
pathp-ends {A = A} P Q e j = com A (∂ j) λ where
  i (j = i0) → P i
  i (j = i1) → Q i
  i (i = i0) → e j

-- pcom→∙ bridges the ternary composite pcom (sym p) q r to the
-- binary chain p ∙ q ∙ r, via pcom.unique against cat.lcoh.
pcom→∙
  : ∀ {u} {A : Type u} {a b c d : A}
    (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  → pcom (sym p) q r ≡ p ∙ q ∙ r
pcom→∙ p q r = pcom.unique
  (sym p) q r
  (p ∙ q ∙ r , cat.lcoh p q r)

```

## Groupoid Laws

```agda

module Path {A : Type u} where
  unitl : {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
  unitl p i j = cat.rfill refl p j (~ i)

  unitr : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  unitr p i j = cat.fill p refl j (~ i)

  invl : {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
  invl p i j = hcom (∂ j ∨ i) (λ k _ → p (~ j ∨ k))

  invr : {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
  invr p = invl (sym p)

  assoc : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
        → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  assoc p q r = ap fst comp
    module assoc where
    private
      comp = HComposite.unique (sym p) q r
        ((p ∙ (q ∙ r)) , cat.lcoh p q r)
        ((p ∙ q) ∙ r , cat.rcoh p q r)

    fill : SquareP (λ i j → q j ≡ comp i .fst j) (cat.lcoh p q r) refl (cat.rcoh p q r) refl
    fill = ap snd comp

  idem : ∀ {u} {A : Type u} (x : A) → refl ∙ refl ≡ refl {x = x}
  idem x = ap fst comp
    module idem where
    private
      comp = HComposite.unique (refl {x = x}) refl refl
        (refl ∙ refl , cat.fill (refl {x = x}) refl)
        (refl , refl)

    fill : SquareP (λ i j → x ≡ comp i .fst j) (cat.fill (λ _ → x) (λ _ → x)) refl refl refl
    fill = ap snd comp

  unitl-filler
    : {x y : A} (p : x ≡ y) → I → I → I → A
  unitl-filler p k j i = cat.rfill refl p j (~ i ∧ k)

  unitr-filler
    : {x y : A} (p : x ≡ y) → I → I → I → A
  unitr-filler p k j i = cat.fill p refl j (~ i ∧ k)

  invl-filler
    : {x y : A} (p : x ≡ y) → I → I → I → A
  invl-filler p l i j = hfil (∂ j ∨ i) l (λ k _ → p (~ j ∨ k))

  invr-filler
    : {x y : A} (p : x ≡ y) → (l i j : I) → A
  invr-filler p l i j = invl-filler (sym p) l i j

  open cat
  hsqueeze : {x y : A} {p q : x ≡ y} → p ∙ refl ≡ refl ∙ q → p ≡ q
  hsqueeze {p} {q} h = pcom (unitr p) h (unitl q)

  vsqueeze : {x y : A} {p q : x ≡ y} → refl ∙ p ≡ q ∙ refl → p ≡ q
  vsqueeze {p} {q} h = pcom (unitl p) h (unitr q)

  paste-refl : {w x y z : A}
         → (p : w ≡ x) (q : w ≡ y) (r : y ≡ z) (s : x ≡ z) (c : x ≡ y)
         → (H : Square p refl q c)
         → (K : Square s c r refl)
         → p ∙ s ≡ q ∙ r
  paste-refl {w} {x} {y} {z} p q r s c H K i j = hcom (∂ j ∨ ~ i) λ where
    k (j = i0) → w
    k (i = i0) → cat.fill p s j k
    k (j = i1) → K i k
    k (k = i0) → H i j

  lwhisker : {x y z : A} (p : x ≡ y) {q r : y ≡ z} → q ≡ r → p ∙ q ≡ p ∙ r
  lwhisker p = ap (p ∙_)

  rwhisker : {x y z : A} {p q : x ≡ y} (r : y ≡ z) → p ≡ q → p ∙ r ≡ q ∙ r
  rwhisker r = ap (_∙ r)

  loop-refl : {x y : A} (p : x ≡ y) (q : y ≡ y)
            → Square p refl p q → q ≡ refl
  loop-refl p q sq i j = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → conn p q j k
    k (i = i1) → p (j ∨ k)
    k (j = i0) → p k
    k (j = i1) → q (i ∨ k)
    k (k = i0) → sq i j

  commutes : {w x y z : A}
           → (p : w ≡ x) (q : x ≡ z) (r : w ≡ y) (s : y ≡ z)
           → Square p r s q → p ∙ q ≡ r ∙ s
  commutes {w} p q r s sq i j = hcom (∂ j ∨ ~ i) λ where
    k (j = i0) → p (~ i ∧ ~ k)
    k (j = i1) → s (~ i ∨ k)
    k (i = i0) → rfill p q j k
    k (k = i0) → sq j (~ i)

  -- move an inverse across the composite: sym p ∙ q ≡ r iff q ≡ p ∙ r
  switch : {x y z : A} {p : x ≡ y} {q : x ≡ z} {r : y ≡ z}
         → sym p ∙ q ≡ r → q ≡ p ∙ r
  switch {p = p} {q} h =
    sym (unitl q)
    ∙ ap (_∙ q) (sym (invr p))
    ∙ sym (assoc p (sym p) q)
    ∙ ap (p ∙_) h

  grp-cancel
    : {a b c : A}
      (p : b ≡ a) (q : c ≡ b)
    → (sym p ∙ sym q) ∙ (q ∙ p) ≡ refl
  grp-cancel p q =
    pcom (sym (assoc (sym p ∙ sym q) q p))
      (ap (_∙ p)
        (pcom (assoc (sym p) (sym q) q)
          (ap (sym p ∙_) (invl q))
          (unitr (sym p))))
      (invl p)

  -- left-cancel an inverted-then-plain prefix off a longer composite
  lc : {a b c : A} (p : a ≡ b) (s : b ≡ c) → sym p ∙ p ∙ s ≡ s
  lc p s = assoc (sym p) p s ∙ ap (_∙ s) (invl p) ∙ unitl s

  -- right-cancel a plain-then-inverted suffix off a longer composite
  rc : {a b c : A} (q : b ≡ c) (t : a ≡ b) → (t ∙ q) ∙ sym q ≡ t
  rc q t = sym (assoc t q (sym q)) ∙ ap (t ∙_) (invr q) ∙ unitr t

  -- a self-path composed onto a path and returning it must be trivial
  wind : {a b : A} (p : a ≡ b) (θ : b ≡ b) → p ≡ p ∙ θ → refl ≡ θ
  wind p θ P = sym (invl p) ∙ ap (sym p ∙_) P ∙ lc p θ

slide : {a b c : A} (p : a ≡ b) (q : b ≡ c)
      → PathP (λ i → a ≡ q i) p (p ∙ q)
slide p q = transpose (cat.fill p q)

cone : {x y z : A} (q : y ≡ z) (r : x ≡ z)
     → Square q (q ∙ sym r) r (λ _ → z)
cone q r i j = hcom (∂ i ∨ j) λ where
  k (i = i0) → q (j ∧ k)
  k (i = i1) → r (j ∨ ~ k)
  k (j = i1) → q (i ∨ k)
  k (k = i0) → q i

cocone : {x y z : A} (p : x ≡ y) (q : x ≡ z)
    → Square p (λ _ → x) q (sym p ∙ q)
cocone {x} p q i j = hcom (∂ i ∨ ~ j) λ where
  k (i = i0) → p j
  k (j = i0) → x
  k (i = i1) → q (j ∧ k)
  k (k = i0) → p (~ i ∧ j)

-- comp-pathp₂-rfill: the displaced cat.rfill for a binary family —
-- sections over the two base rfill squares, glued along their hfil
-- interiors. The composite side is comp-pathp₂ definitionally: at
-- j = i1 the base rfill systems are pcom's systems for refl-headed
-- composition, so the tower is comp-pathp₂'s com on the nose.
comp-pathp₂-rfill
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {b₀ b₁ b₂ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i) (qb i)) h₁ h₂)
  → SquareP (λ i j → F (cat.rfill pa qa i j) (cat.rfill pb qb i j))
      (λ j → P (~ j)) Q (λ _ → h₂)
      (comp-pathp₂ F pa qa pb qb P Q)
comp-pathp₂-rfill {X = X} {Y = Y} F pa qa pb qb P Q i j =
  com (λ k → F (hfil (∂ i ∨ ~ j) k sa) (hfil (∂ i ∨ ~ j) k sb))
      (∂ i ∨ ~ j) λ where
    k (j = i0) → Q (i ∧ k)
    k (i = i0) → P (~ j)
    k (i = i1) → Q k
    k (k = i0) → P (i ∨ ~ j)
  where
    sa : Sys (∂ i ∨ ~ j) X
    sa k (j = i0) = qa (i ∧ k)
    sa k (i = i0) = pa (~ j)
    sa k (i = i1) = qa k
    sa k (k = i0) = pa (i ∨ ~ j)
    sb : Sys (∂ i ∨ ~ j) Y
    sb k (j = i0) = qb (i ∧ k)
    sb k (i = i0) = pb (~ j)
    sb k (i = i1) = qb k
    sb k (k = i0) = pb (i ∨ ~ j)

-- comp-pathp₂-unitl: the displaced Path.unitl for a binary
-- family — the refl-headed comp-pathp₂ collapses to its second
-- line over the base unitl squares. Path.unitl is the transposed
-- cat.rfill at a refl head, so the displaced mate is the
-- transposed comp-pathp₂-rfill at the refl-headed instance; every
-- boundary is definitional (the inner PathP endpoints are the
-- rfill square's left and right columns).
comp-pathp₂-unitl
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {a₀ a₁ : X} (p : a₀ ≡ a₁) {b₀ b₁ : Y} (q : b₀ ≡ b₁)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁}
    (Q : PathP (λ i → F (p i) (q i)) h₀ h₁)
  → PathP (λ m → PathP (λ i → F (Path.unitl p m i) (Path.unitl q m i))
                 h₀ h₁)
          (comp-pathp₂ F refl p refl q refl Q)
          Q
comp-pathp₂-unitl F p q Q m i =
  comp-pathp₂-rfill F refl p refl q refl Q i (~ m)

-- comp-pathp₂-commutes: the displaced Path.commutes for a binary
-- family — a line of sections between the two comp-pathp₂
-- composites, over the base commutes squares, glued along their
-- hfil interiors; the i0 wall is comp-pathp₂-rfill, whose
-- composite side lands the lid on comp-pathp₂ on the nose
comp-pathp₂-commutes
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {wa xa ya za : X} (pa : wa ≡ xa) (qa : xa ≡ za)
    (ra : wa ≡ ya) (sa : ya ≡ za)
    {wb xb yb zb : Y} (pb : wb ≡ xb) (qb : xb ≡ zb)
    (rb : wb ≡ yb) (sb : yb ≡ zb)
    (sqa : Square pa ra sa qa) (sqb : Square pb rb sb qb)
    {h₀ : F wa wb} {hx : F xa xb} {hy : F ya yb} {h₁ : F za zb}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ hx)
    (Q : PathP (λ i → F (qa i) (qb i)) hx h₁)
    (R : PathP (λ i → F (ra i) (rb i)) h₀ hy)
    (S : PathP (λ i → F (sa i) (sb i)) hy h₁)
  → PathP (λ j → PathP (λ i → F (sqa j i) (sqb j i)) (R j) (Q j)) P S
  → PathP (λ i → PathP (λ j → F (Path.commutes pa qa ra sa sqa i j)
                                (Path.commutes pb qb rb sb sqb i j))
                       h₀ h₁)
          (comp-pathp₂ F pa qa pb qb P Q)
          (comp-pathp₂ F ra sa rb sb R S)
comp-pathp₂-commutes {X = X} {Y = Y} F pa qa ra sa pb qb rb sb sqa sqb
  P Q R S SQ i j =
  com (λ k → F (hfil (∂ j ∨ ~ i) k ca) (hfil (∂ j ∨ ~ i) k cb))
      (∂ j ∨ ~ i) λ where
    k (j = i0) → P (~ i ∧ ~ k)
    k (j = i1) → S (~ i ∨ k)
    k (i = i0) → comp-pathp₂-rfill F pa qa pb qb P Q j k
    k (k = i0) → SQ j (~ i)
  where
    ca : Sys (∂ j ∨ ~ i) X
    ca k (j = i0) = pa (~ i ∧ ~ k)
    ca k (j = i1) = sa (~ i ∨ k)
    ca k (i = i0) = cat.rfill pa qa j k
    ca k (k = i0) = sqa j (~ i)
    cb : Sys (∂ j ∨ ~ i) Y
    cb k (j = i0) = pb (~ i ∧ ~ k)
    cb k (j = i1) = sb (~ i ∨ k)
    cb k (i = i0) = cat.rfill pb qb j k
    cb k (k = i0) = sqb j (~ i)

-- comp-pathp₂-unique: the displaced HComposite.path for a binary
-- family — two displaced composites over the same displaced walls,
-- each gluing over one of two base HComposites, are identified over
-- the base uniqueness square. The com runs along the hfil interiors
-- of the two base path hcoms with the displaced cells as m-walls;
-- at m = i0/i1 it caps on the cells' lids, and the j-walls are the
-- constant endpoints, exactly as the base path square's sides are
-- tube faces of its own hcom.
comp-pathp₂-unique
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {xa wa ya za : X} {pa : xa ≡ wa} {qa : xa ≡ ya} {ra : ya ≡ za}
    {xb wb yb zb : Y} {pb : xb ≡ wb} {qb : xb ≡ yb} {rb : yb ≡ zb}
    (αa βa : HComposite pa qa ra) (αb βb : HComposite pb qb rb)
    {hx : F xa xb} {hw : F wa wb} {hy : F ya yb} {hz : F za zb}
    (P : PathP (λ k → F (pa k) (pb k)) hx hw)
    (Q : PathP (λ j → F (qa j) (qb j)) hx hy)
    (R : PathP (λ k → F (ra k) (rb k)) hy hz)
    {S : PathP (λ j → F (αa .fst j) (αb .fst j)) hw hz}
    {T : PathP (λ j → F (βa .fst j) (βb .fst j)) hw hz}
    (C : SquareP (λ j k → F (αa .snd j k) (αb .snd j k)) P Q R S)
    (D : SquareP (λ j k → F (βa .snd j k) (βb .snd j k)) P Q R T)
  → SquareP (λ m j → F (HComposite.path pa qa ra αa βa m j)
                       (HComposite.path pb qb rb αb βb m j))
      S (λ _ → hw) T (λ _ → hz)
comp-pathp₂-unique {X = X} {Y = Y} F
  {pa = pa} {qa} {ra} {pb = pb} {qb} {rb}
  αa βa αb βb P Q R C D m j =
  com (λ k → F (hfil (∂ m ∨ ∂ j) k ua) (hfil (∂ m ∨ ∂ j) k ub))
      (∂ m ∨ ∂ j) λ where
    k (m = i0) → C j k
    k (m = i1) → D j k
    k (j = i0) → P k
    k (j = i1) → R k
    k (k = i0) → Q j
  where
    ua : Sys (∂ m ∨ ∂ j) X
    ua k (m = i0) = αa .snd j k
    ua k (m = i1) = βa .snd j k
    ua k (j = i0) = pa k
    ua k (j = i1) = ra k
    ua k (k = i0) = qa j
    ub : Sys (∂ m ∨ ∂ j) Y
    ub k (m = i0) = αb .snd j k
    ub k (m = i1) = βb .snd j k
    ub k (j = i0) = pb k
    ub k (j = i1) = rb k
    ub k (k = i0) = qb j

-- comp-pathp₂-lcoh: the displaced cat.lcoh for a binary family —
-- sections over the two base lcoh squares, glued along their hfil
-- interiors; the i = i1 wall is comp-pathp₂-fill of the tail pair,
-- and at j = i1 the base systems are pcom's for the refl-headed
-- outer composite, so the lid is the right-nested comp-pathp₂ on
-- the nose.
comp-pathp₂-lcoh
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {a₀ a₁ a₂ a₃ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂) (ra : a₂ ≡ a₃)
    {b₀ b₁ b₂ b₃ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂) (rb : b₂ ≡ b₃)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂} {h₃ : F a₃ b₃}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i) (qb i)) h₁ h₂)
    (R : PathP (λ i → F (ra i) (rb i)) h₂ h₃)
  → SquareP (λ i j → F (cat.lcoh pa qa ra i j) (cat.lcoh pb qb rb i j))
      (λ j → P (~ j)) Q R
      (comp-pathp₂ F pa (qa ∙ ra) pb (qb ∙ rb) P
        (comp-pathp₂ F qa ra qb rb Q R))
comp-pathp₂-lcoh {X = X} {Y = Y} F pa qa ra pb qb rb P Q R i j =
  com (λ k → F (hfil (∂ i ∨ ~ j) k la) (hfil (∂ i ∨ ~ j) k lb))
      (∂ i ∨ ~ j) λ where
    k (i = i0) → P (~ j)
    k (i = i1) → comp-pathp₂-fill F qa ra qb rb Q R j k
    k (j = i0) → Q (i ∧ k)
    k (k = i0) → P (i ∨ ~ j)
  where
    la : Sys (∂ i ∨ ~ j) X
    la k (i = i0) = pa (~ j)
    la k (i = i1) = cat.fill qa ra k j
    la k (j = i0) = qa (i ∧ k)
    la k (k = i0) = pa (i ∨ ~ j)
    lb : Sys (∂ i ∨ ~ j) Y
    lb k (i = i0) = pb (~ j)
    lb k (i = i1) = cat.fill qb rb k j
    lb k (j = i0) = qb (i ∧ k)
    lb k (k = i0) = pb (i ∨ ~ j)

-- comp-pathp₂-rcoh: the displaced cat.rcoh for a binary family —
-- the k = i0 cap is comp-pathp₂-rfill of the head pair, whose
-- composite side is the left-nested inner comp-pathp₂; at j = i1
-- the base systems are pcom's for the outer composite at the rfill
-- lid, so the lid is the left-nested comp-pathp₂ on the nose.
comp-pathp₂-rcoh
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {a₀ a₁ a₂ a₃ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂) (ra : a₂ ≡ a₃)
    {b₀ b₁ b₂ b₃ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂) (rb : b₂ ≡ b₃)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂} {h₃ : F a₃ b₃}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i) (qb i)) h₁ h₂)
    (R : PathP (λ i → F (ra i) (rb i)) h₂ h₃)
  → SquareP (λ i j → F (cat.rcoh pa qa ra i j) (cat.rcoh pb qb rb i j))
      (λ j → P (~ j)) Q R
      (comp-pathp₂ F (pa ∙ qa) ra (pb ∙ qb) rb
        (comp-pathp₂ F pa qa pb qb P Q) R)
comp-pathp₂-rcoh {X = X} {Y = Y} F pa qa ra pb qb rb P Q R i j =
  com (λ k → F (hfil (∂ i ∨ ~ j) k ca) (hfil (∂ i ∨ ~ j) k cb))
      (∂ i ∨ ~ j) λ where
    k (i = i0) → P (~ j)
    k (i = i1) → R (j ∧ k)
    k (j = i0) → Q i
    k (k = i0) → comp-pathp₂-rfill F pa qa pb qb P Q i j
  where
    ca : Sys (∂ i ∨ ~ j) X
    ca k (i = i0) = pa (~ j)
    ca k (i = i1) = ra (j ∧ k)
    ca k (j = i0) = qa i
    ca k (k = i0) = cat.rfill pa qa i j
    cb : Sys (∂ i ∨ ~ j) Y
    cb k (i = i0) = pb (~ j)
    cb k (i = i1) = rb (j ∧ k)
    cb k (j = i0) = qb i
    cb k (k = i0) = cat.rfill pb qb i j

-- comp-pathp₂-assoc: the displaced Path.assoc for a binary family —
-- the two nestings of comp-pathp₂ are identified over the base
-- assoc squares. Path.assoc is HComposite.unique at the lcoh/rcoh
-- witnesses, so the displaced mate is comp-pathp₂-unique at the
-- displaced lcoh/rcoh cells, whose lids are the two nestings on
-- the nose; every boundary is definitional.
comp-pathp₂-assoc
  : ∀ {u v w} {X : Type u} {Y : Type v} (F : X → Y → Type w)
    {a₀ a₁ a₂ a₃ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂) (ra : a₂ ≡ a₃)
    {b₀ b₁ b₂ b₃ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂) (rb : b₂ ≡ b₃)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂} {h₃ : F a₃ b₃}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i) (qb i)) h₁ h₂)
    (R : PathP (λ i → F (ra i) (rb i)) h₂ h₃)
  → PathP (λ m → PathP (λ i → F (Path.assoc pa qa ra m i)
                                (Path.assoc pb qb rb m i))
                 h₀ h₃)
      (comp-pathp₂ F pa (qa ∙ ra) pb (qb ∙ rb) P
        (comp-pathp₂ F qa ra qb rb Q R))
      (comp-pathp₂ F (pa ∙ qa) ra (pb ∙ qb) rb
        (comp-pathp₂ F pa qa pb qb P Q) R)
comp-pathp₂-assoc F pa qa ra pb qb rb P Q R =
  comp-pathp₂-unique F
    ((pa ∙ (qa ∙ ra)) , cat.lcoh pa qa ra)
    (((pa ∙ qa) ∙ ra) , cat.rcoh pa qa ra)
    ((pb ∙ (qb ∙ rb)) , cat.lcoh pb qb rb)
    (((pb ∙ qb) ∙ rb) , cat.rcoh pb qb rb)
    (λ k → P (~ k)) Q R
    (comp-pathp₂-lcoh F pa qa ra pb qb rb P Q R)
    (comp-pathp₂-rcoh F pa qa ra pb qb rb P Q R)

-- comp-pathp₂-map: a fiberwise map under comp-pathp₂ — hcom does
-- not commute with fiberwise application definitionally, so the
-- image of the composite and the composite of the images are
-- identified by one com along the base fill towers, with the two
-- fillers (the F-filler's image and the G-filler) as the m-walls;
-- at m = i0/i1 the fil cap at i1 lands the two composites on the
-- nose. The binary-family displacement of pcom.map.
comp-pathp₂-map
  : ∀ {u v w w'} {X : Type u} {Y : Type v}
    (F : X → Y → Type w) (G : X → Y → Type w')
    (f : ∀ {x y} → F x y → G x y)
    {a₀ a₁ a₂ : X} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
    {b₀ b₁ b₂ : Y} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂)
    {h₀ : F a₀ b₀} {h₁ : F a₁ b₁} {h₂ : F a₂ b₂}
    (P : PathP (λ i → F (pa i) (pb i)) h₀ h₁)
    (Q : PathP (λ i → F (qa i) (qb i)) h₁ h₂)
  → (λ i → f (comp-pathp₂ F pa qa pb qb P Q i))
  ≡ comp-pathp₂ G pa qa pb qb (λ i → f (P i)) (λ i → f (Q i))
comp-pathp₂-map F G f pa qa pb qb {h₀ = h₀} P Q m i =
  com (λ j → G (cat.fill pa qa i j) (cat.fill pb qb i j))
      (∂ i ∨ ∂ m) λ where
    j (i = i0) → f h₀
    j (i = i1) → f (Q j)
    j (j = i0) → f (P i)
    j (m = i0) → f (comp-pathp₂-fill F pa qa pb qb P Q j i)
    j (m = i1) → comp-pathp₂-fill G pa qa pb qb
                   (λ i → f (P i)) (λ i → f (Q i)) j i

```

## Chain Reasoning

```agda

module Chain where
  begin_ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
  begin p = p

  _≡⟨⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ p = p

  _≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
          → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ∙ q

  _≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
           → y ≡ x → y ≡ z → x ≡ z
  x ≡˘⟨ p ⟩ q = sym p ∙ q

  _∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
  x ∎ = refl

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  3 _∎

open Chain public

```

## Triangles

```agda

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

Given `p q : x ≡ y` and `α : p ≡ q`, we get a square
`Square {w=y, x=x, y=x, z=y} p refl q refl` — refl top and bottom,
`p` left, `q` right.

```agda

path→square
  : {A : Type u} {x y : A} {p q : x ≡ y}
  → p ≡ q → Square {w = y} {x = x} {y = x} {z = y} p refl q refl
path→square α i j = α i j
{-# INLINE path→square #-}

```

Square and HCell are definitionally the same with different argument
conventions. The symmetry operations `hflip` and `vflip` are defined
in Core.Base for HCell. The `Square p q r s` convention is: `p` left,
`q` top, `r` right, `s` bottom.

```agda

square-sym-h
  : {A : Type u} {w x y z : A}
    {p : x ≡ w} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
  → Square p q r s → Square r (sym q) p (sym s)
square-sym-h sq i j = sq (~ i) j
{-# INLINE square-sym-h #-}

square-sym-v
  : {A : Type u} {w x y z : A}
    {p : x ≡ w} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
  → Square p q r s → Square (sym p) s (sym r) q
square-sym-v sq i j = sq i (~ j)
{-# INLINE square-sym-v #-}

```

## Dependent ap over composition

```agda

ap-comp-dep
  : ∀ {u v} {A : Type u} {B : A → Type v}
    {x y z : A} (f : (a : A) → B a)
    (p : x ≡ y) (q : y ≡ z)
  → PathP (λ i → PathP (λ j → B (cat.fill p q j i))
      (f x) (f (q i)))
    (ap f p) (ap f (p ∙ q))
ap-comp-dep f p q i j = f (cat.fill p q j i)

```
