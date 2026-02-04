Simplicial sets: spines, the SSet record, and the segal map.

Credit: TOTBWF, "Segal conditions" gist
(https://gist.github.com/TOTBWF/018347c1ef1da6cd9e7a43f2e4295513)

Adapted to kitcat conventions and cubical Agda idioms.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.SSet.Base where

open import Core.Type
open import Core.Base hiding (∂)
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base
open import Core.Kan
open import Core.Equiv
open import Core.Trait.Trunc
open import Core.Transport

open Nat using (_<_; _≤_; s<s; suc; step)

private variable
  u v : Level
  m n k : Nat

```

## Spines

A `Spine H n` is a sequence of `n` composable morphisms in a
hom-family `H : X -> X -> Type`, together with all intermediate
vertices. A 0-spine is a single vertex; a (S n)-spine extends an
existing spine by prepending one morphism.

We define `vertex` mutually with `Spine` by matching on the `fin`
constructor directly (rather than using `fin-view`) so that the
definition reduces definitionally and dependent types in `edge` etc.
work out.

```agda

data Spine
  {u v} {X : Type u} (H : X -> X -> Type v)
  : Nat -> Type (u ⊔ v)

vertex
  : ∀ {u v} {X : Type u} {H : X -> X -> Type v} {n}
  -> Fin (S n) -> Spine H n -> X

data Spine {X = X} H where
  [_] : X -> Spine H Z
  _⨾_ : ∀ {n} {x : X}
       -> (s : Spine H n)
       -> H x (vertex fzero s)
       -> Spine H (S n)

infixl 5 _⨾_

vertex _ [ x ] = x
vertex fzero (_⨾_ {x = x} s h) = x
vertex (fin (S k) ⦃ bounded = forget p ⦄) (_⨾_ s h) =
  vertex (fin k ⦃ forget (Nat.lt.peel _ p) ⦄) s

```

## Edge extraction

Extract the i-th edge from a spine. Edge i connects
`vertex (weaken i)` to `vertex (fsuc i)`.

```agda

edge
  : ∀ {u v} {X : Type u} {H : X -> X -> Type v} {n}
  -> (i : Fin n) -> (s : Spine H n)
  -> H (vertex (weaken i) s) (vertex (fsuc i) s)
edge i (s ⨾ h) with fin-view i
... | vz = h
... | vs j = edge j s

```

## PathP combinator for spines

```agda

_⨾ₚ_/ₚ_
  : ∀ {u v n} {X : Type u} {H : X -> X -> Type v}
  -> {s s' : Spine H n} {x y : X}
     {h : H x (vertex fzero s)} {h' : H y (vertex fzero s')}
  -> (p : s ≡ s')
  -> (q : x ≡ y)
  -> PathP (λ i -> H (q i) (vertex fzero (p i))) h h'
  -> s ⨾ h ≡ s' ⨾ h'
(p ⨾ₚ q /ₚ r) i = p i ⨾ r i

```

## Simplicial sets

A simplicial set is a graded collection of cells with face and
degeneracy operators satisfying the simplicial identities.

For the ordering constraints in simplicial identities we use explicit
natural number ordering on the `lower` projections of the Fin indices,
since kitcat does not have instance search for Fin orderings.

```agda

record SSet (u : Level) : Type (u ₊) where
  no-eta-equality
  field
    Cell : Nat -> Type u
    Cell-is-set : ∀ {n} -> is-set (Cell n)
    ∂ : ∀ {n} -> Fin (S (S n)) -> Cell (S n) -> Cell n
    σ : ∀ {n} -> Fin (S n) -> Cell n -> Cell (S n)

    face-face
      : ∀ {n} {i j : Fin (S (S n))} {x : Cell (S (S n))}
      -> lower i ≤ lower j
      -> ∂ i (∂ (fsuc j) x) ≡ ∂ j (∂ (weaken i) x)

    degen-degen
      : ∀ {n} {i j : Fin (S n)} {x : Cell n}
      -> lower j < lower i
      -> σ (fsuc i) (σ j x) ≡ σ (weaken j) (σ i x)

    face-degen-lt
      : ∀ {n} {i : Fin (S (S n))} {j : Fin (S n)}
        {x : Cell (S n)}
      -> lower i < S (lower j)
      -> ∂ (weaken i) (σ (fsuc j) x) ≡ σ j (∂ i x)

    face-degen-weaken
      : ∀ {n} {i : Fin (S n)} {x : Cell n}
      -> ∂ (weaken i) (σ i x) ≡ x

    face-degen-fsuc
      : ∀ {n} {i : Fin (S n)} {x : Cell n}
      -> ∂ (fsuc i) (σ i x) ≡ x

    face-degen-gt
      : ∀ {n} {i : Fin (S (S n))} {j : Fin (S n)}
        {x : Cell (S n)}
      -> lower j < lower i
      -> ∂ (fsuc i) (σ (weaken j) x) ≡ σ j (∂ i x)

```

### Objects and 1-cells

Objects are 0-cells. A 1-cell from x to y is a 1-cell whose
source face is x and target face is y.

```agda

  Ob : Type u
  Ob = Cell Z

  1-Cell : Ob -> Ob -> Type u
  1-Cell x y = Σ f ∶ Cell 1 , (∂ fzero f ≡ x) × (∂ flast f ≡ y)

  retarget : ∀ {x y y'} -> y ≡ y' -> 1-Cell x y -> 1-Cell x y'
  retarget p (f , s , t) = f , s , t ∙ p

```

A path between 1-cells over a path between endpoints is determined
by a path between the underlying cells, since the boundary data is
propositional.

```agda

  1-cell-pathp
    : ∀ {x x' y y' : Ob}
    -> {f : 1-Cell x y} {g : 1-Cell x' y'}
    -> {p : x ≡ x'} {q : y ≡ y'}
    -> f .fst ≡ g .fst
    -> PathP (λ i -> 1-Cell (p i) (q i)) f g
  1-cell-pathp {f = f} {g} r i .fst = r i
  1-cell-pathp {f = f} {g} {p} {q} r i .snd =
    is-prop→PathP
      (λ i -> ×-is-hlevel 1
        (Cell-is-set (∂ fzero (r i)) (p i))
        (Cell-is-set (∂ flast (r i)) (q i)))
      (f .snd) (g .snd) i

```

### Vertex and edge extraction from higher cells

Given an n-cell f, `ob f i` extracts the i-th vertex (a 0-cell)
by iterated face application.

```agda

  ob : ∀ {n} -> Cell n -> Fin (S n) -> Ob
  ob {n = Z} f _ = f
  ob {n = S n} f fzero = ob (∂ flast f) fzero
  ob {n = S n} f (fin (S k) ⦃ bounded = forget p ⦄) =
    ob (∂ fzero f) (fin k ⦃ forget (Nat.lt.peel _ p) ⦄)

```

Given an (S n)-cell f, `1-cell f i` extracts the i-th 1-cell
connecting adjacent vertices.

```agda

  1-cell
    : ∀ {n} -> (f : Cell (S n))
    -> (i : Fin (S n))
    -> 1-Cell (ob (∂ fzero f) i) (ob (∂ flast f) i)
  1-cell {n = Z} f _ = f , refl , refl
  1-cell {n = S n} f fzero =
    let (h , s , t) = 1-cell (∂ flast f) fzero
        ff = face-face {n = n} {i = fzero} {j = flast} {x = f}
               Nat.lt.z<s
    in h
     , s ∙ ap (λ g -> ob g fzero) ff
     , t
  1-cell {n = S n} f (fin (S k) ⦃ bounded = forget p ⦄) =
    let fk = fin k ⦃ forget (Nat.lt.peel _ p) ⦄
        (h , s , t) = 1-cell (∂ fzero f) fk
        ff = face-face {n = n} {i = fzero} {j = flast} {x = f}
               Nat.lt.z<s
    in h
     , s
     , t ∙ ap (λ g -> ob g fk) (sym ff)

```

### The segal map

The segal map decomposes an n-cell into a spine of n composable
1-cells.

```agda

  segal : ∀ {n} -> Cell n -> Spine 1-Cell n

  segal-src
    : ∀ {n} -> (f : Cell n)
    -> ob f flast ≡ vertex fzero (segal f)

  segal {n = Z} x = [ x ]
  segal {n = S n} f =
    segal (∂ flast f) ⨾
    retarget (segal-src (∂ flast f))
             (1-cell f flast)

  segal-src {n = Z} f = refl
  segal-src {n = S n} f = refl

{-# INLINE SSet.constructor #-}

```
