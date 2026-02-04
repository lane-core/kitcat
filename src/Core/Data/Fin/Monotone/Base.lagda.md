Order-preserving maps between finite types — basic operations.

Identity and composition of monotone maps, face maps (δ), degeneracy
maps (σ), path characterisation, and category laws.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Monotone.Base where

open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base hiding (weaken)
open import Core.Data.Fin.Properties using (fin-path)
open import Core.Data.Fin.Monotone.Type
open import Core.Data.Empty
open import Core.Data.Sum
open import Core.Data.Sigma
open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_)
open import Core.Transport using (is-prop→PathP; subst; is-prop→is-set)
open import Core.Function.Embedding
  using (_↪_; prop→is-embedding)

open Nat

private variable
  m n k l : Nat


```

## Basic operations

```agda

id-mono : n ⇒ n
id-mono .map = id
id-mono .has-is-monotone i j le = le

comp-mono : m ⇒ k → n ⇒ m → n ⇒ k
comp-mono g f .map = g .map ∘ f .map
comp-mono g f .has-is-monotone i j le =
  g .has-is-monotone (f .map i) (f .map j)
    (f .has-is-monotone i j le)

private
  -- Diagrammatic composition (reads left-to-right)
  _⨾_ : n ⇒ m → m ⇒ k → n ⇒ k
  f ⨾ g = comp-mono g f

  infixr 9 _⨾_

```

## Face maps (δ)

Following SSet conventions, the face map `δ i : S n ⇒ n` is the monotone
surjection that duplicates (merges) at position `i`. For `j : Fin (S n)`,
if `j ≤ i` we keep `j`, otherwise we take the predecessor.

This is a "coface" map in the simplicial sense: it goes from a higher
dimension to a lower one by collapsing adjacent vertices.

```agda

-- Bound transformation for low case: j ≤ i and i < n implies j < n
-- j ≤ i means j < S i, and i < n gives S i ≤ n (by s<s), so j < n
δ-lo-bound : ∀ {j i n} → j ≤ i → i < n → j < n
δ-lo-bound ji in' = lt-le-cat ji (lt.s<s in')

-- Compare j : Fin (S n) with i : Fin n for face map
-- Returns: j ≤ i (j < S i) or i < j (S i < S j, i.e., S i ≤ j)
δ-compare : (j : Fin (S n)) (i : Fin n)
           → (lower j < S (lower i)) ⊎ (S (lower i) < S (lower j))
δ-compare j i with cmp (lower j) (lower i)
... | inl p = inl p
... | inr q = inr (lt.s<s q)

-- Explicit result function for δ-map that takes comparison evidence.
-- Proofs can match on comparison results and have the function compute.
δ-result
  : (i : Fin n) (j : Fin (S n))
  → (lower j < S (lower i)) ⊎ (S (lower i) < S (lower j))
  → Fin n
δ-result (fin i' ⦃ bounded = forget ib ⦄)
  (fin j' ⦃ bounded = forget _ ⦄) (inl p) =
  fin j' ⦃ forget (δ-lo-bound p ib) ⦄
δ-result _ j@(fin j' ⦃ bounded = forget _ ⦄) (inr q) =
  fpred j (lt.<→z< (lt.peel j' q))

δ-map : Fin n → Fin (S n) → Fin n
δ-map i j = δ-result i j (δ-compare j i)

δ-result-lo-lower
  : (i : Fin n) (j : Fin (S n)) (p : lower j < S (lower i))
  → lower (δ-result i j (inl p)) ≡ lower j
δ-result-lo-lower _ (fin _) _ = refl

δ-result-hi-lower
  : (i : Fin n) (j : Fin (S n)) (q : S (lower i) < S (lower j))
  → lower (δ-result i j (inr q)) ≡ pred (lower j)
δ-result-hi-lower _ (fin Z) q = ex-falso (lt.¬n<z (lt.peel Z q))
δ-result-hi-lower _ (fin (S _)) _ = refl

δ-mono-raw : (i : Fin n) (j k : Fin (S n)) → lower j ≤ lower k
           → lower (δ-map i j) ≤ lower (δ-map i k)
δ-mono-raw {n} i@(fin i' ⦃ bounded = forget ib ⦄)
           j@(fin j' ⦃ bounded = forget jb ⦄)
           k@(fin k' ⦃ bounded = forget kb ⦄) jk
  with δ-compare j i | δ-compare k i
... | inl _ | inl _ = jk
... | inl ji | inr ik =
  subst (j' ≤_) (sym (δ-result-hi-lower i k ik))
    (le-lt-pred ji (lt.peel k' ik))
... | inr ij | inl ki =
  ex-falso (lt-le-absurd (lt.peel j' ij) (le.cat jk ki))
... | inr ij | inr ik =
  subst (_≤ _) (sym (δ-result-hi-lower i j ij))
    (subst (_ ≤_) (sym (δ-result-hi-lower i k ik))
      (le.pred-mono jk))

δ-mono : (i : Fin n) → is-monotone (δ-map i)
δ-mono i j k (forget jk) = forget (δ-mono-raw i j k jk)

-- Face map: merge/duplicate at position i (surjection)
δ : Fin n → S n ⇒ n
δ i .map = δ-map i
δ i .has-is-monotone = δ-mono i

```

## Degeneracy maps (σ)

Following SSet conventions, the degeneracy map `σ i : n ⇒ S n` is the
unique strictly monotone injection that skips position `i`. For `j : Fin n`,
if `j < i` we keep `j` (with weakened bound), otherwise we use `fsuc j`.

This is a "codegeneracy" map in the simplicial sense: it goes from a lower
dimension to a higher one by inserting a degenerate vertex.

```agda

σ-map : Fin (S n) → Fin n → Fin (S n)
σ-map i j with cmp (lower i) (lower j)
... | inl _ = fsuc j    -- i ≤ j: use successor (shift up)
... | inr _ = weaken j  -- j < i: keep j, weaken bound

σ-mono-raw : (i : Fin (S n)) (j k : Fin n) → lower j ≤ lower k
           → lower (σ-map i j) ≤ lower (σ-map i k)
σ-mono-raw i j k jk with cmp (lower i) (lower j) | cmp (lower i) (lower k)
... | inl _ | inl _ = lt.s<s jk
... | inl ij | inr ki = ex-falso (lt-le-absurd ki (le.cat ij jk))
... | inr _ | inl _ = step jk
... | inr _ | inr _ = jk

σ-mono : (i : Fin (S n)) → is-monotone (σ-map i)
σ-mono i j k (forget jk) = forget (σ-mono-raw i j k jk)

-- Degeneracy map: skip position i (injection)
σ : Fin (S n) → n ⇒ S n
σ i .map = σ-map i
σ i .has-is-monotone = σ-mono i

-- σ-map behavior on low arguments (needed by downstream modules
-- that cannot reduce σ-map's internal with-abstraction)
σ-lower-lo : (i : Fin (S n)) (j : Fin n) → lower j < lower i
           → lower (σ i .map j) ≡ lower j
σ-lower-lo i j lt with cmp (lower i) (lower j)
... | inl le = ex-falso (lt-le-absurd lt le)
... | inr _ = refl

σ-lower-hi : (i : Fin (S n)) (j : Fin n) → lower i ≤ lower j
           → lower (σ i .map j) ≡ S (lower j)
σ-lower-hi i j le with cmp (lower i) (lower j)
... | inl _ = refl
... | inr lt = ex-falso (lt-le-absurd lt le)

σ-map-lo : (i : Fin (S n)) (j : Fin n)
         → lower j < lower i → σ-map i j ≡ weaken j
σ-map-lo i j lt with cmp (lower i) (lower j)
... | inl le = ex-falso (lt-le-absurd lt le)
... | inr _ = refl

σ-map-hi : (i : Fin (S n)) (j : Fin n)
         → lower i ≤ lower j → σ-map i j ≡ fsuc j
σ-map-hi i j le with cmp (lower i) (lower j)
... | inl _ = refl
... | inr lt = ex-falso (lt-le-absurd lt le)

σ-result-lo : (i : Fin (S n)) (j : Fin n) → lower j < lower i
            → lower (σ-map i j) ≡ lower j
σ-result-lo i j lt with cmp (lower i) (lower j)
... | inl le = ex-falso (lt-le-absurd lt le)
... | inr _ = refl

σ-result-hi : (i : Fin (S n)) (j : Fin n) → lower i ≤ lower j
            → lower (σ-map i j) ≡ S (lower j)
σ-result-hi i j le with cmp (lower i) (lower j)
... | inl _ = refl
... | inr lt = ex-falso (lt-le-absurd lt le)

σ-map-lower-lo : (i : Fin (S n)) (j : Fin n)
               → lower j < lower i → lower (σ-map i j) ≡ lower j
σ-map-lower-lo = σ-result-lo

σ-map-lower-hi : (i : Fin (S n)) (j : Fin n)
               → lower i ≤ lower j → lower (σ-map i j) ≡ S (lower j)
σ-map-lower-hi = σ-result-hi

```

## δ-map behavior

```agda

δ-map-lo : (i : Fin n) (j : Fin (S n))
         → (p : lower j < S (lower i))
         → lower (δ-map i j) ≡ lower j
δ-map-lo {n} i@(fin i' ⦃ bounded = forget ib ⦄)
  j@(fin j' ⦃ bounded = forget jb ⦄) p
  with δ-compare j i
... | inl q = δ-result-lo-lower i j q
... | inr q = ex-falso (lt-le-absurd (lt.peel j' q) p)

δ-map-hi : (i : Fin n) (j : Fin (S n))
         → (p : S (lower i) < S (lower j))
         → lower (δ-map i j) ≡ pred (lower j)
δ-map-hi {n} i@(fin i' ⦃ bounded = forget ib ⦄)
  j@(fin j' ⦃ bounded = forget jb ⦄) p
  with δ-compare j i
... | inl q = ex-falso (lt-le-absurd (lt.peel j' p) q)
... | inr q = δ-result-hi-lower i j q

```

## Category laws

Monotone maps form a category. To prove equality of monotone maps,
we show that `is-monotone` is proposition-valued. Since `_≤ᶠ_` is
propositional (wrapped in `Irr`), the monotonicity predicate is also
propositional.

```agda

⇒-path : {f g : m ⇒ n} → f .map ≡ g .map → f ≡ g
⇒-path {m} {n} {f} {g} p i .map = p i
⇒-path {m} {n} {f} {g} p i .has-is-monotone =
  is-prop→PathP (λ i → is-monotone-is-prop (p i))
    (f .has-is-monotone) (g .has-is-monotone) i
  where
    is-monotone-is-prop
      : (f : Fin m → Fin n) → is-prop (is-monotone f)
    is-monotone-is-prop f p q = funext λ i → funext λ j →
      funext λ le → Irr-is-prop (p i j le) (q i j le)

comp-mono-idl : (f : m ⇒ n) → comp-mono id-mono f ≡ f
comp-mono-idl f = ⇒-path refl

comp-mono-idr : (f : m ⇒ n) → comp-mono f id-mono ≡ f
comp-mono-idr f = ⇒-path refl

comp-mono-assoc : (h : k ⇒ l) (g : n ⇒ k) (f : m ⇒ n)
  → comp-mono (comp-mono h g) f ≡ comp-mono h (comp-mono g f)
comp-mono-assoc h g f = ⇒-path refl

```

## σ ordering properties

The degeneracy map σ is strictly monotone: it preserves and reflects
the strict ordering on Fin. The reflection gives an embedding, which
is used by the Catalan simplicial set to transfer strictness through
face maps.

```agda

private
  σ-pres-raw
    : (i : Fin (S n)) (a b : Fin n)
    → lower a < lower b
    → (lower i < S (lower a)) ⊎ (lower a < lower i)
    → (lower i < S (lower b)) ⊎ (lower b < lower i)
    → lower (σ i .map a) < lower (σ i .map b)
  σ-pres-raw i a b lt (inl ia) (inl ib) =
    subst (_< lower (σ i .map b)) (sym (σ-lower-hi i a ia))
      (subst (S (lower a) <_) (sym (σ-lower-hi i b ib))
        (lt.s<s lt))
  σ-pres-raw i a b lt (inl ia) (inr bi) =
    ex-falso (lt-le-absurd (lt.cat lt bi) ia)
  σ-pres-raw i a b lt (inr ai) (inl ib) =
    subst (_< lower (σ i .map b)) (sym (σ-lower-lo i a ai))
      (subst (lower a <_) (sym (σ-lower-hi i b ib))
        (step lt))
  σ-pres-raw i a b lt (inr ai) (inr bi) =
    subst (_< lower (σ i .map b)) (sym (σ-lower-lo i a ai))
      (subst (lower a <_) (sym (σ-lower-lo i b bi))
        lt)

  σ-refl-raw
    : (i : Fin (S n)) (a b : Fin n)
    → lower (σ i .map a) < lower (σ i .map b)
    → (lower i < S (lower a)) ⊎ (lower a < lower i)
    → (lower i < S (lower b)) ⊎ (lower b < lower i)
    → lower a < lower b
  σ-refl-raw i a b lt (inl ia) (inl ib) =
    lt.peel (lower b)
      (subst (_< S (lower b)) (σ-lower-hi i a ia)
        (subst (lower (σ i .map a) <_) (σ-lower-hi i b ib)
          lt))
  σ-refl-raw i a b lt (inl ia) (inr bi) =
    ex-falso (lt.irrefl
      (lt.cat
        (subst (_< lower b) (σ-lower-hi i a ia)
          (subst (lower (σ i .map a) <_) (σ-lower-lo i b bi)
            lt))
        (lt.cat bi ia)))
  σ-refl-raw i a b lt (inr ai) (inl ib) = lt-le-cat ai ib
  σ-refl-raw i a b lt (inr ai) (inr bi) =
    subst (_< lower b) (σ-lower-lo i a ai)
      (subst (lower (σ i .map a) <_) (σ-lower-lo i b bi)
        lt)

σ-preserves-<
  : (i : Fin (S n)) {a b : Fin n}
  → a <ᶠ b → σ i .map a <ᶠ σ i .map b
σ-preserves-< i {a} {b} (forget lt) =
  forget (σ-pres-raw i a b lt
    (cmp (lower i) (lower a))
    (cmp (lower i) (lower b)))

σ-reflects-<
  : (i : Fin (S n)) {a b : Fin n}
  → σ i .map a <ᶠ σ i .map b → a <ᶠ b
σ-reflects-< i {a} {b} (forget lt) =
  forget (σ-refl-raw i a b lt
    (cmp (lower i) (lower a))
    (cmp (lower i) (lower b)))

σ-reflects-<-emb
  : (i : Fin (S n)) {a b : Fin n}
  → (σ i .map a <ᶠ σ i .map b) ↪ (a <ᶠ b)
σ-reflects-<-emb i =
  σ-reflects-< i
  , prop→is-embedding Irr-is-prop
      (is-prop→is-set Irr-is-prop) (σ-reflects-< i)

```

## Simplicial identities

The simplicial identities are the relations between face maps (δ)
and degeneracy maps (σ) that define the simplex category Δ.

### Mixed identities: δ ∘ σ (cancellation)

When j is the same index, δⱼ ∘ σⱼ = id and δⱼ ∘ σⱼ₊₁ = id.
Inserting a point at position j (via σ) and then merging at j (via δ)
gives back the identity.

```agda

δσ-cancel-weaken : (i : Fin n)
  → σ (weaken i) ⨾ δ i ≡ id-mono
δσ-cancel-weaken {n}
  i@(fin i' ⦃ bounded = forget ib ⦄) =
  ⇒-path (funext pointwise)
  where
  pointwise : (j : Fin n)
    → δ-map i (σ-map (weaken i) j) ≡ j
  pointwise j@(fin j' ⦃ bounded = forget jb ⦄)
    with cmp i' j'
  ... | inl le =
    fin-path (δ-map-hi i (fsuc j) (lt.s<s le))
  ... | inr lt =
    fin-path (δ-map-lo i (weaken j) (step lt))

δσ-cancel-fsuc : (i : Fin n)
  → σ (fsuc i) ⨾ δ i ≡ id-mono
δσ-cancel-fsuc {n}
  i@(fin i' ⦃ bounded = forget ib ⦄) =
  ⇒-path (funext pointwise)
  where
  pointwise : (j : Fin n)
    → δ-map i (σ-map (fsuc i) j) ≡ j
  pointwise j@(fin j' ⦃ bounded = forget jb ⦄)
    with cmp (S i') j'
  ... | inl le =
    fin-path (δ-map-hi i (fsuc j) (step le))
  ... | inr lt =
    fin-path (δ-map-lo i (weaken j) lt)

```

### Helper

```agda

private
  lower-restrict
    : (i : Fin (S n)) (p : lower i < n)
    → lower (restrict i p) ≡ lower i
  lower-restrict (fin k) p = refl

```

### Face-face identity (δδ-comm)

The standard identity: δᵢ ∘ δⱼ = δⱼ₋₁ ∘ δᵢ when i ≤ j.

With diagrammatic composition (left-to-right):
- δ (fsuc j) ⨾ δ i : S (S n) ⇒ n
- δ (weaken i) ⨾ δ j : S (S n) ⇒ n

```agda

δδ-comm
  : (i j : Fin n) → lower i ≤ lower j
  → δ (fsuc j) ⨾ δ i ≡ δ (weaken i) ⨾ δ j
δδ-comm {n}
  i@(fin i' ⦃ bounded = forget ib ⦄)
  j@(fin j' ⦃ bounded = forget jb ⦄) i≤j =
  ⇒-path (funext pointwise)
  where
    pointwise
      : (k : Fin (S (S n)))
      → δ-map i (δ-map (fsuc j) k)
      ≡ δ-map j (δ-map (weaken i) k)
    pointwise
      (fin Z ⦃ bounded = forget kb ⦄) =
      fin-path
        (δ-map-lo i
          (δ-result (fsuc j) (fin Z) (inl lt.z<s))
          lt.z<s
         ∙ δ-result-lo-lower
             (fsuc j) (fin Z) lt.z<s
         ∙ sym (δ-result-lo-lower
             (weaken i) (fin Z) lt.z<s)
         ∙ sym (δ-map-lo j
             (δ-result (weaken i) (fin Z)
               (inl lt.z<s))
             lt.z<s))
    pointwise
      (fin (S k') ⦃ bounded = forget kb ⦄) with
      cmp (S k') (S j') | cmp (S k') i'
    ... | inl Sk≤Sj | inl Sk≤i = fin-path
      (δ-map-lo i
        (δ-result (fsuc j)
          (fin (S k') ⦃ forget kb ⦄) (inl Sk≤Sj))
        Sk≤i
       ∙ δ-result-lo-lower (fsuc j)
           (fin (S k') ⦃ forget kb ⦄) Sk≤Sj
       ∙ sym (δ-result-lo-lower (weaken i)
           (fin (S k') ⦃ forget kb ⦄) Sk≤i)
       ∙ sym (δ-map-lo j
           (δ-result (weaken i)
             (fin (S k') ⦃ forget kb ⦄) (inl Sk≤i))
           (le.cat Sk≤i i≤j)))
    ... | inl Sk≤Sj | inr i<Sk = fin-path
      (δ-map-hi i
        (δ-result (fsuc j)
          (fin (S k') ⦃ forget kb ⦄) (inl Sk≤Sj))
        (lt.s<s i<Sk)
       ∙ ap pred (δ-result-lo-lower (fsuc j)
           (fin (S k') ⦃ forget kb ⦄) Sk≤Sj)
       ∙ sym (δ-result-hi-lower (weaken i)
           (fin (S k') ⦃ forget kb ⦄) (lt.s<s i<Sk))
       ∙ sym (δ-map-lo j
           (δ-result (weaken i)
             (fin (S k') ⦃ forget kb ⦄)
             (inr (lt.s<s i<Sk)))
           (lt.peel (S j') Sk≤Sj)))
    ... | inr Sj<Sk | inl Sk<Si =
      ex-falso (lt-le-absurd j<i i≤j)
      where
        j<i : j' < i'
        j<i = lt.peel i' (lt.cat Sj<Sk Sk<Si)
    ... | inr Sj<Sk | inr i<Sk = fin-path
      (δ-map-hi i
        (δ-result (fsuc j)
          (fin (S k') ⦃ forget kb ⦄)
          (inr (lt.s<s Sj<Sk)))
        (lt.s<s i<k)
       ∙ ap pred (δ-result-hi-lower (fsuc j)
           (fin (S k') ⦃ forget kb ⦄)
           (lt.s<s Sj<Sk))
       ∙ sym (ap pred (δ-result-hi-lower (weaken i)
           (fin (S k') ⦃ forget kb ⦄)
           (lt.s<s i<Sk)))
       ∙ sym (δ-map-hi j
           (δ-result (weaken i)
             (fin (S k') ⦃ forget kb ⦄)
             (inr (lt.s<s i<Sk)))
           (lt.s<s j<k)))
      where
        j<k : j' < k'
        j<k = lt.peel k' Sj<Sk
        i<k : i' < k'
        i<k = ≤<→< i≤j j<k
          where
            ≤<→< : ∀ {a b c}
              → a ≤ b → b < c → a < c
            ≤<→< suc q = q
            ≤<→< (step p) q = lt.cat p q

```

### Degeneracy-degeneracy identity (σσ-comm)

The standard identity: σᵢ ; σⱼ₊₁ = σⱼ ; σᵢ when i ≤ j
(diagrammatic order).

```agda

σσ-comm
  : (i j : Fin (S n)) → lower i ≤ lower j
  → σ i ⨾ σ (fsuc j) ≡ σ j ⨾ σ (weaken i)
σσ-comm {n}
  i@(fin i' ⦃ bounded = forget ib ⦄)
  j@(fin j' ⦃ bounded = forget jb ⦄) i≤j =
  ⇒-path (funext pointwise)
  where
    pointwise : (k : Fin n)
      → σ-map (fsuc j) (σ-map i k)
      ≡ σ-map (weaken i) (σ-map j k)
    pointwise
      k@(fin k' ⦃ bounded = forget kb ⦄)
      with cmp i' k' | cmp j' k'
    ... | inl i≤k | inl j≤k = fin-path
      (σ-result-hi (fsuc j) (fsuc k)
        (lt.s<s j≤k)
       ∙ sym (σ-result-hi (weaken i) (fsuc k)
           (step i≤k)))
    ... | inl i≤k | inr k<j = fin-path
      (σ-result-lo (fsuc j) (fsuc k)
        (lt.s<s k<j)
       ∙ sym (σ-result-hi (weaken i) (weaken k)
           i≤k))
    ... | inr k<i | inl j≤k =
      ex-falso (lt-le-absurd j<i i≤j)
      where
        j<i : j' < i'
        j<i = lt-le-cat j≤k (lt.s<s k<i)
    ... | inr k<i | inr k<j = fin-path
      (σ-result-lo (fsuc j) (weaken k)
        (step k<j)
       ∙ sym (σ-result-lo (weaken i) (weaken k)
           k<i))

```

### Mixed face-degeneracy interchange identities

These identities relate face and degeneracy maps when indices differ.
Together with the cancellation cases, they complete the simplicial
identities.

In our setting with diagrammatic composition:
- σ (fsuc j) ⨾ δ (weaken i) ≡ δ i ⨾ σ j when i < j
- σ (weaken j) ⨾ δ (fsuc i) ≡ δ i ⨾ σ j when j < i

```agda

δσ-interchange-lt
  : (i : Fin n) (j : Fin (S n)) → lower i < lower j
  → σ (fsuc j) ⨾ δ (weaken i) ≡ δ i ⨾ σ j
δσ-interchange-lt {n}
  i@(fin i' ⦃ bounded = forget ib ⦄)
  j@(fin j' ⦃ bounded = forget jb ⦄) i<j =
  ⇒-path (funext pointwise)
  where
    z<j : Z < j'
    z<j = lt.<→z< i<j

    pointwise-z
      : δ-map (weaken i) (σ-map (fsuc j) (fin Z))
      ≡ σ-map j (δ-map i (fin Z))
    pointwise-z with cmp (S j') Z
    ... | inl Sj≤Z =
      ex-falso (lt.¬n<z (lt.peel Z Sj≤Z))
    ... | inr Z<Sj with cmp Z (S i')
    ... | inl Z<Si = fin-path
      (δ-map-lo (weaken i)
        (weaken (fin Z)) lt.z<s
       ∙ sym (σ-result-lo j
           (δ-result i (fin Z) (inl lt.z<s))
           z<j))
    ... | inr Si<Z = ex-falso (lt.¬n<z Si<Z)

    pointwise : (k : Fin (S n))
      → δ-map (weaken i) (σ-map (fsuc j) k)
      ≡ σ-map j (δ-map i k)
    pointwise (fin Z ⦃ bounded = forget _ ⦄) =
      pointwise-z
    pointwise
      k@(fin (S k'') ⦃ bounded = forget kb ⦄)
      with cmp (S j') (S k'') | cmp (S k'') i'
    ... | inl Sj≤Sk | inl Sk≤i =
      ex-falso (lt.irrefl i<i)
      where
        Sj≤i : S j' ≤ i'
        Sj≤i = le.cat Sj≤Sk Sk≤i
        j<i : j' < i'
        j<i = lt.peel i' Sj≤i
        i<i : i' < i'
        i<i = lt.cat i<j j<i
    ... | inl Sj≤Sk | inr i<Sk = fin-path
      (δ-map-hi (weaken i) (fsuc k)
        (lt.s<s (step i<Sk))
       ∙ sym (σ-result-hi j
           (δ-result i k (inr (lt.s<s i<Sk)))
           j≤k''))
      where
        j≤k'' : j' ≤ k''
        j≤k'' = lt.peel (S k'') Sj≤Sk
    ... | inr Sk<Sj | inl Sk≤i = fin-path
      (δ-map-lo (weaken i) (weaken k) Sk≤i
       ∙ sym (σ-result-lo j
           (δ-result i k (inl Sk≤i)) Sk<j))
      where
        Sk<j : S k'' < j'
        Sk<j = lt-le-cat Sk≤i (lt.s<s i<j)
    ... | inr Sk<Sj | inr i<Sk = fin-path
      (δ-map-hi (weaken i) (weaken k)
        (lt.s<s i<Sk)
       ∙ sym (σ-result-lo j
           (δ-result i k (inr (lt.s<s i<Sk)))
           k<j))
      where
        k<j : k'' < j'
        k<j = lt.peel j' Sk<Sj

δσ-interchange-gt
  : (i : Fin n) (j : Fin (S n)) → lower j < lower i
  → σ (weaken j) ⨾ δ (fsuc i) ≡ δ i ⨾ σ j
δσ-interchange-gt {n}
  i@(fin i' ⦃ bounded = forget ib ⦄)
  j@(fin j' ⦃ bounded = forget jb ⦄) j<i =
  ⇒-path (funext pointwise)
  where
    pointwise : (k : Fin (S n))
      → δ-map (fsuc i) (σ-map (weaken j) k)
      ≡ σ-map j (δ-map i k)
    pointwise
      k@(fin k' ⦃ bounded = forget kb ⦄)
      with cmp j' k' | cmp k' i'
    ... | inl j≤k | inl k≤i = fin-path
      (δ-map-lo (fsuc i) (fsuc k)
        (lt.s<s k≤i)
       ∙ sym (σ-result-hi j
           (δ-result i k (inl k≤i)) j≤k))
    pointwise
      (fin Z ⦃ bounded = forget _ ⦄)
      | inl _ | inr i<Z =
      ex-falso (lt.¬n<z i<Z)
    pointwise
      k@(fin (S k'') ⦃ bounded = forget _ ⦄)
      | inl j≤Sk | inr i<Sk = fin-path
      (δ-map-hi (fsuc i) (fsuc k)
        (lt.s<s (lt.s<s i<Sk))
       ∙ sym (σ-result-hi j
           (δ-result i k (inr (lt.s<s i<Sk)))
           j≤k''))
      where
        j≤k'' : j' ≤ k''
        j≤k'' = lt.cat j<i i<Sk
    ... | inr k<j | inl k≤i = fin-path
      (δ-map-lo (fsuc i) (weaken k)
        (step k≤i)
       ∙ sym (σ-result-lo j
           (δ-result i k (inl k≤i)) k<j))
    ... | inr k<j | inr i<k =
      ex-falso (lt.irrefl i<i')
      where
        k<i : k' < i'
        k<i = lt.cat k<j j<i
        i<i' : i' < i'
        i<i' = lt.cat i<k k<i

```
