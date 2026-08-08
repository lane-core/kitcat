The cross-pair grammar. The unit here is an ordered pair of objects,
matching the arity of `reflect`: the datum at `(x , y)` is one
endo-edge at each end, `sand` is the recognition equation over the
connecting homs, and the two fibers read one endpoint each. The
gluing clauses ask adjacent satisfying instances to assemble into
diagonal ones. At one object the mixed instance built from two
inhabitants is a term both of their conditions read, and it
identifies their pairs. The last section states the edge-indexed
conjunct: the family readback of a recognized framing, whose diagonal
fragment repeats the framing's own sandwich.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Gluing where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Degenerate.Shape
```

## The grammar

The cross pair at `(x , y)` holds an endo-edge at `x` first and one
at `y` second. The sandwich at the pair is the recognition equation
over the connecting homs. Each action map anchors at one component,
and its fiber over the second projection reads that endpoint alone.

```agda
module grammar {o h} (G : virtual-graph o h) where
  open virtual-graph G

  cross : ob → ob → Type h
  cross x y = hom x x × hom y y

  sand : (x y : ob) → cross x y → Type h
  sand x y c = (f : hom x y) → reflect f ((x , c .fst) , (y , c .snd)) ≡ f

  coact : (x : ob) → hom x x → hom x x → (γ : coterm x) → hom x (γ .fst)
  coact x u e γ = reflect e ((x , u) , γ)

  act : (y : ob) → hom y y → hom y y → (t : term y) → hom (t .fst) y
  act y v e s = reflect e (s , (y , v))

  inv⁻ : (x : ob) → hom x x → Type (o ⊔ h)
  inv⁻ x u = is-contr (fiber (coact x u) snd)

  inv⁺ : (y : ob) → hom y y → Type (o ⊔ h)
  inv⁺ y v = is-contr (fiber (act y v) snd)

  is-cross : (x y : ob) → cross x y → Type (o ⊔ h)
  is-cross x y c = sand x y c × (inv⁻ x (c .fst) × inv⁺ y (c .snd))
```

## The gluing clauses

The characteristic, stated over the sandwich alone: adjacent
satisfying instances glue. An instance at `(x , y)` glues with one
into `x`, and the first component of the central instance pairs with
the second component of the adjacent one to give a diagonal instance
at `x`. The mirror form reads an adjacent instance out of `y`.

```agda
  characteristic : Type (o ⊔ h)
  characteristic =
      ( {a x y : ob} (c : cross x y) (d : cross a x)
        → sand x y c → sand a x d → sand x x (c .fst , d .snd) )
    × ( {x y b : ob} (c : cross x y) (d : cross y b)
        → sand x y c → sand y b d → sand y y (d .fst , c .snd) )

  mixing : characteristic → {x : ob} (P Q : cross x x)
         → sand x x P → sand x x Q → sand x x (P .fst , Q .snd)
  mixing X P Q SP SQ = X .fst P Q SP SQ
```

Read at a fixed pair as the central instance, with the adjacent input
at the sandwich level, the characteristic splits into two clauses.
The predicate on a cross pair is the fibers, the sandwich, and those
two clauses; the recognizing type asks every ordered pair of objects
for a cross pair carrying it.

```agda
  glue⁻ : (x y : ob) → cross x y → Type (o ⊔ h)
  glue⁻ x y c = {a : ob} (d : cross a x)
              → sand a x d → sand x x (c .fst , d .snd)

  glue⁺ : (x y : ob) → cross x y → Type (o ⊔ h)
  glue⁺ x y c = {b : ob} (d : cross y b)
              → sand y b d → sand y y (d .fst , c .snd)

  pred : (x y : ob) → cross x y → Type (o ⊔ h)
  pred x y c = is-cross x y c × (glue⁻ x y c × glue⁺ x y c)

  recognized : Type (o ⊔ h)
  recognized = (x y : ob) → Σ c ∶ cross x y , pred x y c
```

A diagonal sandwich forces each fiber point to the other component of
its pair, one fiber per hand.

```agda
  point⁻ : {x : ob} (u v : hom x x) → sand x x (u , v)
         → (w : fiber (coact x u) snd) → w .fst ≡ v
  point⁻ {x} u v R w = sym (R (w .fst)) ∙ happly (w .snd) (x , v)

  point⁺ : {x : ob} (u v : hom x x) → sand x x (u , v)
         → (w : fiber (act x v) snd) → w .fst ≡ u
  point⁺ {x} u v R w = sym (R (w .fst)) ∙ happly (w .snd) (x , u)
```

## Two inhabitants at one object

Over an arbitrary carrier, take two inhabitants of the recognizing Σ
at one object. The gluing clause of the first read at the second
gives a sandwich for the mixed pair. One coact fiber point then sits
under two sandwiches, the first inhabitant's own and the mixed one,
which identifies the second components; one act fiber point does the
same for the first components. So the two pairs are equal.

```agda
  module play {x : ob} (P Q : Σ c ∶ cross x x , pred x x c) where
    uP tP uQ tQ : hom x x
    uP = P .fst .fst
    tP = P .fst .snd
    uQ = Q .fst .fst
    tQ = Q .fst .snd

    SP : sand x x (uP , tP)
    SP = P .snd .fst .fst

    SQ : sand x x (uQ , tQ)
    SQ = Q .snd .fst .fst

    mixed : sand x x (uP , tQ)
    mixed = P .snd .snd .fst (Q .fst) SQ

    w⁻ : fiber (coact x uP) snd
    w⁻ = P .snd .fst .snd .fst .center

    w⁺ : fiber (act x tQ) snd
    w⁺ = Q .snd .fst .snd .snd .center

    pin-t : tP ≡ tQ
    pin-t = sym (point⁻ uP tP SP w⁻) ∙ point⁻ uP tQ mixed w⁻

    pin-u : uP ≡ uQ
    pin-u = sym (point⁺ uP tQ mixed w⁺) ∙ point⁺ uQ tQ SQ w⁺

    pair-path : P .fst ≡ Q .fst
    pair-path i = pin-u i , pin-t i
```

## The edge-indexed conjunct

A connecting edge is one term that two families' readback conditions
both read, and over an arbitrary carrier the two conditions give
exactly the agreement of the edge's two sandwiches.

```agda
module coherence {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open shape G

  agree : (P Q : family) → rbᶠ P → rbᶠ Q
        → ∀ {x y} (f : hom x y)
        → reflect f ((x , P x .fst) , (y , P y .snd))
        ≡ reflect f ((x , Q x .fst) , (y , Q y .snd))
  agree P Q RP RQ f = RP f ∙ sym (RQ f)
```

The per-object shape carries the diagonal instances of family
readback and nothing else. The edge-indexed condition is the family
readback of the recognized framing, a conjunct beside the framing
rather than a clause inside it.

```agda
  coherent : is-framed → Type (o ⊔ h)
  coherent R = rbᶠ (frame-of R)

  is-coherent-deductive-system-depreciated : Type (o ⊔ h)
  is-coherent-deductive-system-depreciated =
    reflect-is-embedding G × (Σ R ∶ is-framed , cuts R × coherent R)
```
