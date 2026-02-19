Lane Biocini
February 2026

# Categories via Representable Embeddings

A category is defined by embedding its morphisms into their
post-composition actions on a function type. Each `f : hom x y`
is faithfully represented by the function `(_ ⨾ f) : hom w x → hom w y`.
Since function types carry algebraic structure for free—composition
is definitionally associative and unital—the category laws reduce
to the statement that two morphisms with the same post-composition
behavior must be equal, which is exactly what the embedding
guarantees via propositional fibers.

## The fields

The first three fields give the basic structure:

  - `repr : hom x y ↪ (∀ {w} → hom w x → hom w y)` embeds
    each morphism into its post-composition action
  - `unital : fiber (repr .fst) id` places the identity
    function in the image, giving the identity morphism
  - `coh f g : fiber (repr .fst) (repr .fst g ∘ repr .fst f)`
    closes the image under composition, giving `f ⨾ g`

From these, both unit laws and associativity are derived by
injectivity of the embedding. For instance, `f ⨾ idn` and `f`
both represent the same function (since `repr idn = id`), so
they're equal. Both `(f ⨾ g) ⨾ h` and `f ⨾ (g ⨾ h)` represent
`repr h ∘ repr g ∘ repr f`, so they inhabit the same fiber;
since fibers of an embedding are propositions, they must be
equal.

Two further fields make the definition self-dual:

  - `repr-op-emb` asserts that pre-composition
    `f ↦ (f ⨾ _)` is an embedding
  - `yon-emb` asserts that post-composition
    `f ↦ (_ ⨾ f)` is an embedding

Both are propositions (`is-embedding` is always a proposition).
The opposite category swaps `repr` with the derived `repr-op`
and exchanges the two embedding fields: pre-composition in the
opposite is post-composition in the original, and vice versa.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.Function.Embedding

record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    repr
      : ∀ {x y} → hom x y ↪ (∀ {w} → hom w x → hom w y)
    unital
      : ∀ {x} → fiber (repr {x} {x} .fst) id
    coh
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → fiber (repr .fst) (repr .fst g ∘ repr .fst f)

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = coh f g .fst

  yon-map
    : ∀ {x y} → hom x y → (∀ {z} → hom y z → hom x z)
  yon-map f g = f ⨾ g

  field
    yon-emb
      : ∀ {w x} → is-embedding (yon-map {w} {x})

-- is-category : ∀ {o h} → Σ O ∶ Type o , (O → O → Type h) → Type (o ⊔ h)
-- is-category (ob , hom)
--   = Σ repr ∶ (∀ {x y} → hom x y ↪ (∀ {w} → hom w x → hom w y))
--   , (∀ {x} → fiber (repr {x} {x} .fst) λ {w} → id)
--   × (Σ coh ∶ (∀ {x y z} (f : hom x y) (g : hom y z) → fiber (repr {x} {z} .fst) (λ {w} → repr {y} {z} .fst g ∘ repr {x} {y} .fst f))
--   , ∀ {w x : ob} → is-embedding (λ (f : hom w x) (g : hom x {!!}) → coh {w} {x} f g .fst))

module Cat {o} {h} (C : category o h) where
  open category C
```

## Derived definitions

The representation map `repr .fst` is an embedding, so its fibers
are propositions. This gives injectivity: equal representations
imply equal morphisms. All the category laws reduce to showing
that two representations coincide, then applying injectivity.

```agda
  private
    module R {x} {y} = Emb (repr {x} {y})

  idn : ∀ {x} → hom x x
  idn = unital .fst
```

## Right unit law

`coh f idn .snd` gives a path from `repr .fst (f ⨾ idn)` to
`repr .fst idn ∘ repr .fst f`. Then `unital .snd` collapses
`repr .fst idn` to `id`, recovering `repr .fst f`.

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f = R.inj
    (coh f idn .snd ∙ λ i h → unital .snd i (repr .fst f h))
```

## Left unit law

```agda
  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f = R.inj
    (coh idn f .snd
    ∙ λ i h → repr .fst f (unital .snd i h))
```


## Associativity

Both `(f ⨾ g) ⨾ h` and `f ⨾ (g ⨾ h)` live in a fiber over the
fully-decomposed representation
`λ a → repr .fst h (repr .fst g (repr .fst f a))`.
We build each fiber element and then use propositional fibers to
identify them.

```agda
  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (repr .snd _ lhs rhs)
    where
      decomposed
        : ∀ {v} → hom v _ → hom v _
      decomposed a =
        repr .fst h (repr .fst g (repr .fst f a))

      lhs : fiber (repr .fst) decomposed
      lhs .fst = (f ⨾ g) ⨾ h
      lhs .snd =
        coh (f ⨾ g) h .snd
        ∙ λ i a →
          repr .fst h (coh f g .snd i a)

      rhs : fiber (repr .fst) decomposed
      rhs .fst = f ⨾ (g ⨾ h)
      rhs .snd =
        coh f (g ⨾ h) .snd
        ∙ λ i a →
          coh g h .snd i (repr .fst f a)
```

## Repr-op injectivity

If `f` and `g` compose identically with every morphism on the
right, they must be equal. We instantiate at `idn` and cancel
the units.

```agda
  repr-op-inj
    : ∀ {x y} {f g : hom x y}
    → (∀ {z} (h : hom y z) → f ⨾ h ≡ g ⨾ h)
    → f ≡ g
  repr-op-inj {f = f} {g} p =
    pcom (unitr f) (p idn) (unitr g)
```

## Contravariant representation

The contravariant embedding sends a morphism to its
pre-composition action. The embedding property is the
axiom `yon-emb`.

```agda
  repr-op : ∀ {x y} → hom x y ↪ (∀ {z} → hom y z → hom x z)
  repr-op .fst f g = f ⨾ g
  repr-op .snd = yon-emb

  private
    module Rop {x} {y} = Emb (repr-op {x} {y})
```




## Derived op-structure

The unit and coherence witnesses for `repr-op` follow from
`unitl` and `assoc`.

```agda
  unital-op : ∀ {x} → fiber (repr-op {x} {x} .fst) id
  unital-op .fst = idn
  unital-op .snd i g = unitl g i

  coh-op
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → fiber (repr-op .fst)
        (repr-op .fst f ∘ repr-op .fst g)
  coh-op f g .fst = f ⨾ g
  coh-op f g .snd i h = assoc f g h i

```
WIP

## The opposite category

The opposite swaps `repr` with the derived `repr-op` and
exchanges the two embedding fields. Pre-composition in `op`
is post-composition in `C` (so `op.repr-op-emb = C.yon-emb`),
and post-composition in `op` is pre-composition in `C`
(so `op.yon-emb = C.repr-op-emb`).

```agda
--   private module C = category C

--   op : category o h
--   op .category.ob          = ob
--   op .category.hom         = λ x y → C.hom y x
--   op .category.repr        = repr-op
--   op .category.unital      = unital-op
--   op .category.coh         = λ f g → coh-op g f
--   op .category.yon-emb f (h , p) (k , q) =
--     {!C.coh ? ? .fst!}
--     where
--       f0 : (λ g → g ⨾ h) ≡ (λ g → g ⨾ k)
--       f0 = {!!}
--       w0 : h ≡ k
--       w0 = pcom (unitl h) {!!} (unitl k)

-- module _ {o h} (C : category o h) where
--   private module C = category C renaming (_⨾_ to seq)

--   -- op-invo : op (op C) ≡ C
--   -- op-invo i .category.ob = C.ob
--   -- op-invo i .category.hom = C.hom
--   -- op-invo i .category.repr .fst g f = {!!}
--   -- op-invo i .category.repr .snd = {!!}
--   -- op-invo i .category.unital = {!!}
--   -- op-invo i .category.coh = {!!}
--   -- op-invo i .category.yon-emb = {!!}
```
