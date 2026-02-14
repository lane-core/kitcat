Lane Biocini
January 2026

Embeddings: functions with propositional fibers.
Some definitions and proofs are derived from: 1Lab.Function.Embedding, 1Lab.Equiv (Amélia Liao et al.; January 2026)
Left-cancellable maps and monomorphisms merged from Core.Function.LeftCancellable.
Credit: TypeTopology, UF.LeftCancellable (Escardo)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Function.Embedding where

open import Core.Transport
open import Core.Equiv
open import Core.Base
open import Core.Path
open import Core.Type
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Kan
open import Core.Sub
open import Core.HLevel
open import Core.Trait.Trunc using (Σ-prop-path) public
open import Core.Data.Fin.Type using (Fin; lower)
open import Core.Data.Fin.Properties using (fin-path)
open import Core.Data.Nat using (Nat)
```

## Core Definitions

```agda
module _ {u v} {A : Type u} {B : Type v} where
  injective : (A → B) → Type _
  injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  left-cancellable : (A → B) → Type _
  left-cancellable = injective

  is-embedding : (A → B) → Type _
  is-embedding f = ∀ y → is-prop (fiber f y)
```

## Bundled Type

```agda
_↪_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ↪ B = Σ f ∶ (A → B) , is-embedding f
infix 6 _↪_

Emb : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Emb = _↪_
```

## Bundled monomorphism

Credit: TypeTopology, UF.LeftCancellable (Escardo)

```agda
record _↣_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  no-eta-equality
  field
    fun   : A → B
    is-lc : ∀ {x y} → fun x ≡ fun y → x ≡ y

infix 6 _↣_

{-# INLINE _↣_.constructor #-}
```

## Left-cancellable closure properties

```agda
lc-comp
  : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
  → {f : A → B} {g : B → C}
  → left-cancellable f → left-cancellable g
  → left-cancellable (g ∘ f)
lc-comp f-lc g-lc p = f-lc (g-lc p)

section→lc
  : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
  → has-retraction f → left-cancellable f
section→lc (r , η) {x} {y} p = sym (η x) ∙ ap r p ∙ η y

equiv→lc
  : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
  → is-equiv f → left-cancellable f
equiv→lc e = section→lc (Equiv.inv (_ , e) , Equiv.unit (_ , e))
```

## Conversions

```agda
module _ {u v} {A : Type u} {B : Type v} where
  -- Adapted from 1Lab.Function.Embedding (Amélia Liao et al.; January 2026)
  injective→is-embedding : is-set B → (f : A → B) → injective f → is-embedding f
  injective→is-embedding bset f inj y (x , p) (x' , q) =
    Σ-prop-path (λ _ → bset _ _) (inj (p ∙ sym q))

  -- Adapted from 1Lab.Function.Embedding (Amélia Liao et al.; January 2026)
  has-prop-fibers→injective : (f : A → B) → is-embedding f → injective f
  has-prop-fibers→injective f emb p = ap fst (emb _ (_ , p) (_ , refl))
```

## Module Interface

```agda
module Emb {u v} {A : Type u} {B : Type v} (e : A ↪ B) where
  fwd : A → B
  fwd = e .fst

  prop-fibers : is-embedding fwd
  prop-fibers = e .snd

  inj : ∀ {x y} → fwd x ≡ fwd y → x ≡ y
  inj = has-prop-fibers→injective fwd prop-fibers
```

## From Equivalences

```agda
-- Equivalences are embeddings (unbundled)
is-equiv→is-embedding
  : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
  → is-equiv f → is-embedding f
is-equiv→is-embedding e y = is-contr→is-prop (e .eqv-fibers y)

-- Equivalences are embeddings (bundled)
equiv→embedding : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A ↪ B
equiv→embedding e = e .fst , is-equiv→is-embedding (e .snd)

-- Alias for clarity
embedding→injective
  : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
  → is-embedding f → injective f
embedding→injective {f = f} = has-prop-fibers→injective f

id-emb : ∀ {u} {A : Type u} → A ↪ A
id-emb = equiv→embedding equiv
```

## Composition

Fibers of composites decompose as Σ-types of fibers.
See 1Lab.Equiv (fibre-∘-≃) and 1Lab.Function.Embedding (∘-is-embedding).

```agda
private
  -- Σ over a prop of props is a prop
  Σ-prop² : ∀ {u v} {A : Type u} {B : A → Type v}
          → is-prop A → ((a : A) → is-prop (B a)) → is-prop (Σ B)
  Σ-prop² aprop bprop (a₁ , b₁) (a₂ , b₂) i =
    aprop a₁ a₂ i , is-prop→PathP (λ j → bprop (aprop a₁ a₂ j)) b₁ b₂ i

-- Adapted from 1Lab.Equiv (Amélia Liao et al.; January 2026)
fiber-comp : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
           → (f : A → B) (g : B → C) (c : C)
           → fiber (g ∘ f) c ≃ (Σ (b , _) ∶ fiber g c , fiber f b)
fiber-comp f g c = iso→equiv fwd bwd sec retr
  where
    fwd : fiber (g ∘ f) c → Σ (b , _) ∶ fiber g c , fiber f b
    fwd (a , p) = (f a , p) , (a , refl)

    bwd : (Σ (b , _) ∶ fiber g c , fiber f b) → fiber (g ∘ f) c
    bwd ((b , q) , (a , r)) = a , ap g r ∙ q

    sec : (x : fiber (g ∘ f) c) → bwd (fwd x) ≡ x
    sec (a , p) i = a , unitl p i

    retr : (y : Σ (b , _) ∶ fiber g c , fiber f b) → fwd (bwd y) ≡ y
    retr ((b , q) , (a , r)) i = (r i , lemma i) , (a , λ j → r (i ∧ j))
      where
        lemma : PathP (λ i → g (r i) ≡ c) (ap g r ∙ q) q
        lemma i j = hcom (∂ i ∨ ∂ j) λ where
          k (i = i0) → cat.fill (ap g r) q j k
          k (i = i1) → q (j ∧ k)
          k (j = i0) → g (r i)
          k (j = i1) → q k
          k (k = i0) → g (r (i ∨ j))

-- Adapted from 1Lab.Function.Embedding (Amélia Liao et al.; January 2026)
_∙↪_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} → A ↪ B → B ↪ C → A ↪ C
(f , ef) ∙↪ (g , eg) = g ∘ f , λ c →
  is-prop-equiv (fiber-comp f g c) (Σ-prop² (eg c) (λ (b , _) → ef b))

infixr 9 _∙↪_
```

## Embedding Characterizations

### ap preserves embedding

Embeddings make `ap` an equivalence (stronger than just an embedding).
Credit: Adapted from 1Lab.Function.Embedding (embedding→cancellable).

```agda
embedding→ap-equiv
  : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
  → is-embedding f
  → {x y : A}
  → is-equiv (ap f {x} {y})
embedding→ap-equiv {A = A} {B = B} {f = f} emb {x} {y} =
  iso→equiv (ap f) inv unit counit .snd
  where
    fib-prop : is-prop (fiber f (f y))
    fib-prop = emb (f y)

    -- The inverse: given q : f x ≡ f y, extract the path x ≡ y from fiber
    inv : f x ≡ f y → x ≡ y
    inv q = ap fst (fib-prop (x , q) (y , refl))

    -- Unit: inv (ap f p) ≡ p
    unit : (p : x ≡ y) → inv (ap f p) ≡ p
    unit p = ap (ap fst) path-unique ∙ ap-fst-lifted
      where
        -- The path in fiber from (x, ap f p) to (y, refl) via p
        lifted-p : (x , ap f p) ≡ (y , refl)
        lifted-p i = p i , sq i
          where
            sq : PathP (λ i → f (p i) ≡ f y) (ap f p) refl
            sq i j = hcom (∂ i ∨ ∂ j) λ where
              k (i = i0) → f (p j)
              k (i = i1) → f y
              k (j = i0) → f (p i)
              k (j = i1) → f y
              k (k = i0) → f (p (i ∨ j))

        -- fib-prop gives the same path (up to path in paths)
        path-unique : fib-prop (x , ap f p) (y , refl) ≡ lifted-p
        path-unique = is-prop→is-set fib-prop _ _ _ _

        ap-fst-lifted : ap fst lifted-p ≡ p
        ap-fst-lifted = refl

    -- Counit: ap f (inv q) ≡ q
    counit : (q : f x ≡ f y) → ap f (inv q) ≡ q
    counit q = α
      where
        fp : (x , q) ≡ (y , refl)
        fp = fib-prop (x , q) (y , refl)

        α : ap f (ap fst fp) ≡ q
        α i j = hcom (∂ i ∨ ∂ j) λ where
          k (i = i0) → fp j .snd (~ k)     -- f y → f (fp j .fst)
          k (i = i1) → q (j ∨ ~ k)          -- f y → q j
          k (j = i0) → q (~ k)              -- f y → f x
          k (j = i1) → f y
          k (k = i0) → f y

ap-is-embedding
  : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
  → is-embedding f
  → {x y : A}
  → is-embedding (ap f {x} {y})
ap-is-embedding emb = is-equiv→is-embedding (embedding→ap-equiv emb)
```

### Left cancellation for embeddings

```agda
embedding-cancel-l
  : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} {f : B → C}
  → is-embedding f
  → is-set B
  → {g h : A → B}
  → f ∘ g ≡ f ∘ h
  → g ≡ h
embedding-cancel-l {f = f} emb B-set {g} {h} fg≡fh =
  funext λ a → has-prop-fibers→injective f emb (happly fg≡fh a)
```

### Σ-types with propositional fibers

```agda
-- First projection from a Σ-type with propositional fibers is an embedding
Σ-prop-embedding
  : ∀ {u v} {A : Type u} {B : A → Type v}
  → ((a : A) → is-prop (B a))
  → is-embedding (fst {B = B})
Σ-prop-embedding {A = A} {B = B} B-prop y =
  retract→is-hlevel 1 decode encode sec (B-prop y)
  where
    encode : fiber (fst {B = B}) y → B y
    encode ((a , b) , p) = subst B p b

    decode : B y → fiber fst y
    decode b = (y , b) , refl

    sec : (fib : fiber fst y) → decode (encode fib) ≡ fib
    sec ((a , b) , p) i = (fst-path i , snd-path i) , third-path i
      where
        fst-path : y ≡ a
        fst-path = sym p

        snd-path : PathP (λ i → B (fst-path i)) (subst B p b) b
        snd-path = is-prop→PathP (λ i → B-prop (fst-path i)) (subst B p b) b

        third-path : PathP (λ i → fst-path i ≡ y) refl p
        third-path i j = p (~ i ∨ j)
```


## Embedding and propositions

```agda
embedding→is-prop
  : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
  → is-embedding f → is-prop B → is-prop A
embedding→is-prop {f = f} emb B-prop a₁ a₂ =
  has-prop-fibers→injective f emb (B-prop _ _)

prop→is-embedding
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-prop A → is-set B
  → (f : A → B) → is-embedding f
prop→is-embedding A-prop B-set f =
  injective→is-embedding B-set f (λ _ → A-prop _ _)

Emb-is-prop
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-prop B → is-prop (A ↪ B)
Emb-is-prop B-prop (f , ef) (g , eg) =
  Σ-prop-path (λ h → Π-is-prop λ y → is-prop-is-prop _)
    (funext λ x → B-prop (f x) (g x))
```


## Fin embeds into Nat

```agda
Fin↪Nat : ∀ {n} → Fin n ↪ Nat
Fin↪Nat .fst = lower
Fin↪Nat .snd = injective→is-embedding Nat.set lower fin-path
```
