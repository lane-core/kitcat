Cubical sets: the CSet record and basic infrastructure.

Adapted from Lib.SSet.Base to the cubical setting. The cube category
is defined in Lib.CSet.Cube with morphisms `m =>[] n = Fin n -> Fin m
+ Bool`. The CSet record is a contravariant presheaf on this category.

Credit: TOTBWF, "Segal conditions" gist
(https://gist.github.com/TOTBWF/018347c1ef1da6cd9e7a43f2e4295513)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.CSet.Base where

open import Core.Type
open import Core.Base hiding (∂)
open import Core.Data.Sigma
open import Core.Data.Bool
open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base
open import Core.Kan
open import Core.Equiv
open import Core.Trait.Trunc
open import Core.Transport

open import Lib.SSet.Base
  using (Spine; [_]; _⨾_; vertex; edge; _⨾ₚ_/ₚ_)

open Nat using (_<_; _≤_; s<s; suc; step)

private variable
  u v : Level
  m n k : Nat

```

## Cubical sets

A cubical set is a graded collection of cells with face and
degeneracy operators satisfying the cubical identities.

Face maps take an additional `Bool` argument selecting the endpoint
(false = 0, true = 1). The presheaf is contravariant, so:
- Face maps `sigma[] k e : n =>[] S n` induce `partial k e : Cell (S n) -> Cell n`
- Degeneracy maps `delta[] k : S n =>[] n` induce `sigma k : Cell n -> Cell (S n)`

```agda

record CSet (u : Level) : Type (u ₊) where
  no-eta-equality
  field
    Cell : Nat -> Type u
    Cell-is-set : ∀ {n} -> is-set (Cell n)
    ∂ : ∀ {n} -> Fin (S n) -> Bool -> Cell (S n) -> Cell n
    σ : ∀ {n} -> Fin (S n) -> Cell n -> Cell (S n)

    face-degen-cancel
      : ∀ {n} {k : Fin (S n)} {e : Bool} {x : Cell n}
      -> ∂ k e (σ k x) ≡ x

    face-face
      : ∀ {n} {i j : Fin (S n)} {ε ε' : Bool}
        {x : Cell (S (S n))}
      -> lower i ≤ lower j
      -> ∂ i ε (∂ (fsuc j) ε' x) ≡ ∂ j ε' (∂ (weaken i) ε x)

    degen-degen
      : ∀ {n} {i j : Fin (S n)} {x : Cell n}
      -> lower i ≤ lower j
      -> σ (weaken i) (σ j x) ≡ σ (fsuc j) (σ i x)

    face-degen-lt
      : ∀ {n} {i j : Fin (S n)} {e : Bool}
        {x : Cell (S n)}
      -> lower i < lower j
      -> ∂ (fsuc j) e (σ (weaken i) x) ≡ σ i (∂ j e x)

    face-degen-gt
      : ∀ {n} {i j : Fin (S n)} {e : Bool}
        {x : Cell (S n)}
      -> lower j < lower i
      -> ∂ (weaken j) e (σ (fsuc i) x) ≡ σ i (∂ j e x)

```

### Objects and 1-cells

Objects are 0-cells. A 1-cell from x to y is a 1-cell whose
true-face is x and false-face is y. This convention matches the
SSet.Base direction: `1-Cell x y` has `partial fzero f = x` and
`partial flast f = y`, where for cubical sets fzero's true-face
is the "later" vertex and fzero's false-face is the "earlier"
vertex. So `1-Cell (later) (earlier)`.

```agda

  Ob : Type u
  Ob = Cell Z

  1-Cell : Ob -> Ob -> Type u
  1-Cell x y =
    Σ f ∶ Cell 1 , (∂ fzero true f ≡ x) × (∂ fzero false f ≡ y)

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
        (Cell-is-set (∂ fzero true (r i)) (p i))
        (Cell-is-set (∂ fzero false (r i)) (q i)))
      (f .snd) (g .snd) i

```

### Vertex extraction from higher cells

Given an n-cell f, `ob f i` extracts the i-th vertex (a 0-cell)
along the main diagonal of the cube. Vertex 0 iterates the
false face of the last dimension. Vertex (S k) takes the true
face of the first dimension, then recurses.

```agda

  ob : ∀ {n} -> Cell n -> Fin (S n) -> Ob
  ob {n = Z} f _ = f
  ob {n = S n} f fzero = ob (∂ flast false f) fzero
  ob {n = S n} f (fin (S k) ⦃ bounded = forget p ⦄) =
    ob (∂ fzero true f) (fin k ⦃ forget (Nat.lt.peel _ p) ⦄)

```

### The segal map

The segal map decomposes an n-cell into a spine of n composable
1-cells. Each step peels off the last dimension: we recurse on
`partial flast false f` and prepend a 1-cell connecting along
that dimension. The segal 1-cell at each step connects
`ob f flast` to `ob (partial flast false f) flast` by iterating
along `partial fzero true` and using face-face to commute past
`partial flast false`.

```agda

  segal-1-cell
    : ∀ {n} -> (f : Cell (S n))
    -> 1-Cell (ob f flast)
              (ob (∂ flast false f) flast)

  segal-1-cell {n = Z} f = f , refl , refl

  segal-1-cell {n = S n} f =
    let (h , s , t) = segal-1-cell (∂ fzero true f)
        ff = face-face {n = n}
               {i = fzero} {j = flast}
               {ε = true} {ε' = false} {x = f}
               Nat.lt.z<s
    in h
     , s
     , t ∙ ap (λ g -> ob g flast) (sym ff)

```

The `segal-src` lemma establishes that `ob f flast` equals the
start vertex of the segal spine. This holds definitionally
because `vertex fzero (s ⨾ h)` reduces to the first component
of `h`, which is `ob f flast` from the segal-1-cell type.

```agda

  segal : ∀ {n} -> Cell n -> Spine 1-Cell n

  segal-src
    : ∀ {n} -> (f : Cell n)
    -> ob f flast ≡ vertex fzero (segal f)

  segal {n = Z} x = [ x ]
  segal {n = S n} f =
    segal (∂ flast false f) ⨾
    retarget (segal-src (∂ flast false f))
             (segal-1-cell f)

  segal-src {n = Z} f = refl
  segal-src {n = S n} f = refl

{-# INLINE CSet.constructor #-}

```
