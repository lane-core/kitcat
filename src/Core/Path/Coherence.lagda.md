Lane Biocini, February 2026

Triangle and pentagon coherence for path composition.
These are the MacLane coherence conditions for the path groupoid,
following Rijke Exercise 5.4. The proofs use contractibility of
HComposite spaces from Core.Kan.

Credit: 1lab, Cat.Bi.Instances.Discrete for the general approach.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Path.Coherence where

open import Core.Base
open import Core.Type using (Level; Type)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Transport.Base using (Singl-contr)
open import Core.Path using (ap-comp)

private
  variable
    u : Level
```

## Triangle identity

The triangle coherence says that the two canonical paths from
`p ∙ (refl ∙ q)` to `p ∙ q` agree:

- Going right via `assoc p refl q` then `ap (_∙ q) (unitr p)`
- Going directly via `ap (p ∙_) (unitl q)`

Both sides lift to paths in `HComposite (sym p) refl q`, which
is contractible by the Kan condition. Contractible types are sets,
so any two paths between the same endpoints coincide.

```agda

module _ {A : Type u} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) where

  private
    HC = HComposite (sym p) refl q

    HC-contr : is-contr HC
    HC-contr = pcom.contr (sym p) refl q

    cell : (r : y ≡ z) → HCell (sym p) refl q (p ∙ r)
    cell r j k = {!!}
     -- hcom (∂ j ∨ ∂ k) λ where
     --   l (j = i0) → p (~ k)
     --   l (j = i1) → q (k ∧ l)
     --   l (k = i0) → y
     --   l (k = i1) → cat.fill p r j l
     --   l (l = i0) → p (j ∨ ~ k)

    e₁ : HC
    e₁ = p ∙ (refl ∙ q) , cell (refl ∙ q)

    e₃ : HC
    e₃ = p ∙ q , cell q

    any-cell : (s : x ≡ z) → HCell (sym p) refl q s
    any-cell s j k = {!!}
      -- hcom (∂ j ∨ ~ k) λ where
      --   l (j = i0) → p (~ k)
      --   l (j = i1) → s (k ∧ l)
      --   l (k = i0) → y
      --   l (l = i0) → p (j ∨ ~ k)

  triangle
    : Path.assoc p refl q ∙ ap (_∙ q) (Path.unitr p)
      ≡ ap (p ∙_) (Path.unitl q)
  triangle = total-contr-unique HC-contr
    (e₁ .snd) (e₃ .snd)
    (Path.assoc p refl q ∙ ap (_∙ q) (Path.unitr p))
    (ap (p ∙_) (Path.unitl q))
    lhs-over rhs-over
    where
    rhs-over
      : PathP (λ i → HCell (sym p) refl q
          (ap (p ∙_) (Path.unitl q) i))
          (e₁ .snd) (e₃ .snd)
    rhs-over i = cell (Path.unitl q i)

    lhs-over
      : PathP (λ i → HCell (sym p) refl q
          ((Path.assoc p refl q ∙ ap (_∙ q) (Path.unitr p)) i))
          (e₁ .snd) (e₃ .snd)
    lhs-over i j k = hcom (∂ i ∨ ∂ j ∨ ~ k) λ where
      l (i = i0) → {!!} -- cell (refl ∙ q) j k
      l (i = i1) → {!!} -- cell q j k
      l (j = i0) → {!!} -- p (~ k)
      l (j = i1) → {!!} -- (Path.assoc p refl q ∙ ap (_∙ q) (Path.unitr p)) i (k ∧ l)
      l (k = i0) → {!!} -- y
      l (l = i0) → {!!} -- p (j ∨ ~ k)
```

## Pentagon identity

The pentagon coherence says that the two canonical paths from
`p ∙ (q ∙ (r ∙ s))` to `((p ∙ q) ∙ r) ∙ s` agree.

```agda

module _ {A : Type u} {v w x y z : A}
  (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z) where

  private
    -- HComposite (sym p) q (r ∙ s)
    HC-contr = pcom.contr (sym p) q (r ∙ s)
    HC-set = is-contr→is-set HC-contr
    lcoh = cat.lcoh p q (r ∙ s)
    rcoh = cat.rcoh p q (r ∙ s)

    e₁ e₂ : HComposite (sym p) q (r ∙ s)
    e₁ = _ , lcoh
    e₂ = _ , rcoh

    path₁₂ : e₁ ≡ e₂
    path₁₂ = HComposite.unique (sym p) q (r ∙ s) e₁ e₂

    sys-L : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-L i j k (i = i0) = p (~ j)
    sys-L i j k (i = i1) = (r ∙ s) j
    sys-L i j k (j = i0) = q i
    sys-L i j k (j = i1) = Path.assoc (p ∙ q) r s k i
    sys-L i j k (k = i0) = rcoh i j

    e₃ : HComposite (sym p) q (r ∙ s)
    e₃ = _ , λ i j → hcom (∂ i ∨ ∂ j) λ k → sys-L i j k

    lift₂₃ : e₂ ≡ e₃
    lift₂₃ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-L i j l

    sys-R₁ : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-R₁ i j k (i = i0) = p (~ j)
    sys-R₁ i j k (i = i1) = (r ∙ s) j
    sys-R₁ i j k (j = i0) = q i
    sys-R₁ i j k (j = i1) =
      ap (p ∙_) (Path.assoc q r s) k i
    sys-R₁ i j k (k = i0) = lcoh i j

    e₄ : HComposite (sym p) q (r ∙ s)
    e₄ = _ , λ i j →
      hcom (∂ i ∨ ∂ j) λ k → sys-R₁ i j k

    lift₁₄ : e₁ ≡ e₄
    lift₁₄ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-R₁ i j l

    sys-R₂ : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-R₂ i j k (i = i0) = p (~ j)
    sys-R₂ i j k (i = i1) = (r ∙ s) j
    sys-R₂ i j k (j = i0) = q i
    sys-R₂ i j k (j = i1) =
      Path.assoc p (q ∙ r) s k i
    sys-R₂ i j k (k = i0) = e₄ .snd i j

    e₅ : HComposite (sym p) q (r ∙ s) -- HC
    e₅ = _ , λ i j →
      hcom (∂ i ∨ ∂ j) λ k → sys-R₂ i j k

    lift₄₅ : e₄ ≡ e₅
    lift₄₅ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-R₂ i j l

    sys-R₃ : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
    sys-R₃ i j k (i = i0) = p (~ j)
    sys-R₃ i j k (i = i1) = (r ∙ s) j
    sys-R₃ i j k (j = i0) = q i
    sys-R₃ i j k (j = i1) =
      ap (_∙ s) (Path.assoc p q r) k i
    sys-R₃ i j k (k = i0) = e₅ .snd i j

    e₆ : HComposite (sym p) q (r ∙ s)
    e₆ = _ , λ i j →
      hcom (∂ i ∨ ∂ j) λ k → sys-R₃ i j k

    lift₅₆ : e₅ ≡ e₆
    lift₅₆ k = _ , λ i j →
      hfil (∂ i ∨ ∂ j) k λ l → sys-R₃ i j l

    lhs-HC : e₁ ≡ e₃
    lhs-HC = path₁₂ ∙ lift₂₃

    rhs-HC : e₁ ≡ e₆
    rhs-HC = lift₁₄ ∙ lift₄₅ ∙ lift₅₆

    bridge : e₆ ≡ e₃
    bridge = is-contr→is-prop HC-contr e₆ e₃

  pentagon
    : Path.assoc p q (r ∙ s) ∙ Path.assoc (p ∙ q) r s
      ≡ ap (p ∙_) (Path.assoc q r s)
        ∙ Path.assoc p (q ∙ r) s
        ∙ ap (_∙ s) (Path.assoc p q r)
  pentagon i j k = hcom (∂ k ∨ ∂ j) {!λ where
    m (k = i0) → ?
    m (k = i1) → ?
    m (j = i0) → ?
    m (j = i1) → ?
    m (m = i0) → α ? ?
    !} where
    α : ap fst lhs-HC ≡ ap fst (rhs-HC ∙ bridge)
    α = ap (ap fst) (HC-set e₁ e₃ lhs-HC (rhs-HC ∙ bridge))
```
