Segal condition: composition, identity, and category laws.

Credit: TOTBWF, "Segal conditions" gist
(https://gist.github.com/TOTBWF/018347c1ef1da6cd9e7a43f2e4295513)

Adapted to kitcat conventions and cubical Agda idioms.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.SSet.Segal where

open import Core.Type hiding (_∘_)
open import Core.Base hiding (∂)
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base
open import Core.Kan hiding (assoc)
open import Core.Equiv
open import Core.Trait.Trunc
open import Core.Transport

open import Lib.SSet.Base
open import Cat.Base

open Nat using (_<_; _≤_; s<s; suc; step)

private variable
  u : Level
  n : Nat

```

## The Segal condition

A simplicial set satisfies the Segal condition when the segal map
(decomposing an n-cell into a spine of composable 1-cells) is an
equivalence for every n. This means that every composable sequence
of 1-cells has a unique filler.

```agda

record Segal {u} (C : SSet u) : Type u where
  no-eta-equality
  open SSet C

  field
    segal-is-equiv : (n : Nat) -> is-equiv (segal {n})

  module segal-equiv (n : Nat) =
    Equiv (segal {n} , segal-is-equiv n)

```

### Composition

Given a composable pair of 1-cells, we obtain a 2-cell by
inverting the segal equivalence, then extract the diagonal as
the composite. The boundary proofs use the face-face identity
together with the segal counit.

```agda

  _∘_ : ∀ {x y z} -> 1-Cell y z -> 1-Cell x y -> 1-Cell x z
  _∘_ {x} {y} {z} f g = h-cell , src-pf , tgt-pf where
    spine : Spine 1-Cell 2
    spine = [ _ ] ⨾ f ⨾ g

    cell : Cell 2
    cell = segal-equiv.inv 2 spine

    coh : segal cell ≡ spine
    coh = segal-equiv.counit 2 spine

    -- The middle face ∂₁ of the 2-cell is the composite.
    -- ∂₁ : Fin 3 -> Cell 2 -> Cell 1
    -- fin 1 : Fin 3, bounded by step suc (1 < 3)
    ∂₁ : Fin (S (S (S Z)))
    ∂₁ = fin 1 ⦃ forget (step suc) ⦄

    h-cell : Cell 1
    h-cell = ∂ ∂₁ cell

    -- face-face at n=0, i=fzero, j=fzero gives:
    --   ∂₀(∂₁ cell) ≡ ∂₀(∂₀ cell)
    -- and vertex 0 of segal cell ≡ x via counit.
    --
    -- face-face at n=0, i=fzero, j=flast gives:
    --   ∂₀(∂₂ cell) ≡ ∂₁(∂₀ cell)
    -- These combine with segal coherence to establish boundaries.

    -- Source: ∂ fzero (∂₁ cell) ≡ x
    -- Via face-face with i=0, j=0:
    --   ∂₀(∂₁ cell) = ∂₀(∂₀ cell) = ob (∂₀ cell) fzero
    -- And segal counit tells us vertex 0 of segal cell = x
    src-pf : ∂ fzero h-cell ≡ x
    src-pf =
      face-face {n = Z} {i = fzero} {j = fzero} {x = cell}
        Nat.le.rx
      ∙ ap (vertex fzero) coh

    -- Target: ∂ flast (∂₁ cell) ≡ z
    -- Via face-face with i=flast, j=flast (eqv : 1 ≤ 1):
    --   ∂₁(∂₂ cell) ≡ ∂₁(∂₁ cell)
    -- So sym gives: ∂₁(∂₁ cell) ≡ ∂₁(∂₂ cell)
    -- Then ∂₂ cell = ∂ flast cell, so ∂₁(∂₂ cell) = ∂ flast(∂ flast cell)
    -- which is vertex 2 of (segal cell), connected to z by counit.
    tgt-pf : ∂ flast h-cell ≡ z
    tgt-pf =
      sym (face-face {n = Z} {i = flast} {j = flast} {x = cell}
             Nat.le.rx)
      ∙ ap (vertex (fin 2 ⦃ forget suc ⦄)) coh

  infixr 9 _∘_

```

### Identity

The identity 1-cell on x is the degeneracy of x.

```agda

  idn : ∀ {x} -> 1-Cell x x
  idn {x} = σ fzero x , face-degen-weaken , face-degen-fsuc

```

### Identity laws and associativity

For `idl` and `idr`, we exhibit a witness 2-cell (a degeneracy
of `f`) whose segal image equals the composition spine, then use
the segal unit to recover the inverse, and extract the middle
face via `face-degen-fsuc` (resp. `face-degen-weaken`). Since
cells are sets, `1-cell-pathp` lifts the underlying cell path to
a path between 1-cells.

```agda

  idl : ∀ {x y} -> (f : 1-Cell x y) -> idn ∘ f ≡ f
  idl {x} {y} f = 1-cell-pathp cell-path where
    spine : Spine 1-Cell 2
    spine = [ _ ] ⨾ idn ⨾ f

    ∂₁ : Fin (S (S (S Z)))
    ∂₁ = fin 1 ⦃ forget (step suc) ⦄

    -- Witness 2-cell: σ₀(f)
    w : Cell 2
    w = σ fzero (f .fst)

    -- ∂₁(w) ≡ f .fst via face-degen-fsuc
    face-w : ∂ ∂₁ w ≡ f .fst
    face-w = face-degen-fsuc

    -- ∂ flast w ≡ idn .fst
    -- face-degen-gt: ∂ (fsuc i) (σ (weaken j) x) ≡ σ j (∂ i x)
    -- with i = flast, j = fzero: ∂ (fin 2) (σ fzero (f .fst)) ≡ σ fzero (∂ flast (f .fst))
    last-face : ∂ flast w ≡ idn .fst
    last-face =
      face-degen-gt {i = flast} {j = fzero} suc
      ∙ ap (σ fzero) (f .snd .snd)

    -- ∂ fzero w ≡ f .fst via face-degen-weaken
    first-face : ∂ fzero w ≡ f .fst
    first-face = face-degen-weaken

    -- segal (idn .fst) ≡ [ y ] ⨾ idn
    inner-spine-eq : segal (idn .fst) ≡ [ y ] ⨾ idn
    inner-spine-eq =
      ap [_] face-degen-fsuc
      ⨾ₚ face-degen-weaken
      /ₚ 1-cell-pathp {p = face-degen-weaken}
                       {q = face-degen-fsuc} refl

    -- segal (∂ flast w) ≡ [ y ] ⨾ idn
    inner-eq : segal (∂ flast w) ≡ [ y ] ⨾ idn
    inner-eq = ap segal last-face ∙ inner-spine-eq

    -- The outer edge underlying cell: ∂ fzero w ≡ f .fst
    last-edge-cell
      : (retarget (segal-src (∂ flast w))
                   (1-cell w flast)) .fst
        ≡ f .fst
    last-edge-cell = first-face

    -- Source vertex of outer edge: ∂ fzero (∂ fzero w) ≡ x
    src-vtx : ∂ fzero (∂ fzero w) ≡ x
    src-vtx = ap (∂ fzero) first-face ∙ f .snd .fst

    -- segal w ≡ spine
    spine-eq : segal w ≡ spine
    spine-eq =
      inner-eq
      ⨾ₚ src-vtx /ₚ 1-cell-pathp last-edge-cell

    -- segal-equiv.inv 2 spine ≡ w
    inv-path : segal-equiv.inv 2 spine ≡ w
    inv-path =
      ap (segal-equiv.inv 2) (sym spine-eq)
      ∙ segal-equiv.unit 2 w

    cell-path : ∂ ∂₁ (segal-equiv.inv 2 spine) ≡ f .fst
    cell-path = ap (∂ ∂₁) inv-path ∙ face-w

  idr : ∀ {x y} -> (f : 1-Cell x y) -> f ∘ idn ≡ f
  idr {x} {y} f = 1-cell-pathp cell-path where
    spine : Spine 1-Cell 2
    spine = [ _ ] ⨾ f ⨾ idn

    ∂₁ : Fin (S (S (S Z)))
    ∂₁ = fin 1 ⦃ forget (step suc) ⦄

    -- Witness 2-cell: σ_last(f)
    w : Cell 2
    w = σ flast (f .fst)

    -- ∂₁(w) ≡ f .fst via face-degen-weaken
    face-w : ∂ ∂₁ w ≡ f .fst
    face-w = face-degen-weaken

    -- ∂ flast w ≡ f .fst via face-degen-fsuc
    last-face : ∂ flast w ≡ f .fst
    last-face = face-degen-fsuc

    -- ∂ fzero w ≡ idn .fst
    first-face : ∂ fzero w ≡ idn .fst
    first-face =
      face-degen-lt {i = fzero} {j = fzero} (suc {m = Z})
      ∙ ap (σ fzero) (f .snd .fst)

    -- segal (f .fst) ≡ [ y ] ⨾ f
    inner-spine-eq : segal (f .fst) ≡ [ y ] ⨾ f
    inner-spine-eq =
      ap [_] (f .snd .snd)
      ⨾ₚ f .snd .fst
      /ₚ 1-cell-pathp {p = f .snd .fst}
                       {q = f .snd .snd} refl

    -- segal (∂ flast w) ≡ [ y ] ⨾ f
    inner-eq : segal (∂ flast w) ≡ [ y ] ⨾ f
    inner-eq = ap segal last-face ∙ inner-spine-eq

    -- Source vertex of outer edge: ∂ fzero (∂ fzero w) ≡ x
    src-vtx : ∂ fzero (∂ fzero w) ≡ x
    src-vtx =
      ap (∂ fzero) (face-degen-lt {i = fzero} {j = fzero}
        (suc {m = Z}))
      ∙ ap (λ z → ∂ fzero (σ fzero z)) (f .snd .fst)
      ∙ face-degen-weaken

    last-edge-cell
      : (retarget (segal-src (∂ flast w))
                   (1-cell w flast)) .fst
        ≡ idn .fst
    last-edge-cell = first-face

    -- segal w ≡ spine
    spine-eq : segal w ≡ spine
    spine-eq =
      inner-eq
      ⨾ₚ src-vtx /ₚ 1-cell-pathp last-edge-cell

    -- segal-equiv.inv 2 spine ≡ w
    inv-path : segal-equiv.inv 2 spine ≡ w
    inv-path =
      ap (segal-equiv.inv 2) (sym spine-eq)
      ∙ segal-equiv.unit 2 w

    cell-path : ∂ ∂₁ (segal-equiv.inv 2 spine) ≡ f .fst
    cell-path = ap (∂ ∂₁) inv-path ∙ face-w

  assoc
    : ∀ {w x y z}
    -> (f : 1-Cell y z) (g : 1-Cell x y) (h : 1-Cell w x)
    -> f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  assoc {w} {x} {y} {z} f g h = 1-cell-pathp cell-path where
    -- Abbreviations for face indices
    ∂₁₂ : Fin (S (S (S Z)))
    ∂₁₂ = fin 1 ⦃ forget (step suc) ⦄

    -- The 3-dimensional segal inverse: unique 3-cell whose
    -- spine is [ z ] ⨾ f ⨾ g ⨾ h.
    spine₃ : Spine 1-Cell 3
    spine₃ = [ _ ] ⨾ f ⨾ g ⨾ h

    τ : Cell 3
    τ = segal-equiv.inv 3 spine₃

    coh₃ : segal τ ≡ spine₃
    coh₃ = segal-equiv.counit 3 spine₃

    -- The key face-face identity relating the two compositions
    ff : ∂ ∂₁₂ (∂ (fsuc ∂₁₂) τ) ≡ ∂ ∂₁₂ (∂ (weaken ∂₁₂) τ)
    ff = face-face {n = S Z} {i = ∂₁₂} {j = ∂₁₂} {x = τ}
           Nat.le.rx

    -- Composition cells and their segal counits
    spine-gh : Spine 1-Cell 2
    spine-gh = [ _ ] ⨾ g ⨾ h

    cell-gh : Cell 2
    cell-gh = segal-equiv.inv 2 spine-gh

    coh-gh : segal cell-gh ≡ spine-gh
    coh-gh = segal-equiv.counit 2 spine-gh

    spine-fg : Spine 1-Cell 2
    spine-fg = [ _ ] ⨾ f ⨾ g

    cell-fg : Cell 2
    cell-fg = segal-equiv.inv 2 spine-fg

    coh-fg : segal cell-fg ≡ spine-fg
    coh-fg = segal-equiv.counit 2 spine-fg

    spine-l : Spine 1-Cell 2
    spine-l = [ _ ] ⨾ f ⨾ (g ∘ h)

    cell-l : Cell 2
    cell-l = segal-equiv.inv 2 spine-l

    spine-r : Spine 1-Cell 2
    spine-r = [ _ ] ⨾ (f ∘ g) ⨾ h

    cell-r : Cell 2
    cell-r = segal-equiv.inv 2 spine-r

    face₂τ : Cell 2
    face₂τ = ∂ (fsuc ∂₁₂) τ

    face₁τ : Cell 2
    face₁τ = ∂ (weaken ∂₁₂) τ

    segal-cancel : ∀ {n} {a b : Cell n} -> segal a ≡ segal b
                 -> a ≡ b
    segal-cancel {n} {a} {b} p =
      sym (segal-equiv.unit n a)
      ∙ ap (segal-equiv.inv _) p
      ∙ segal-equiv.unit n b

    -- Spine projection: extract inner spine from (s ⨾ h)
    spine-inner
      : ∀ {u v n} {X : Type u} {H : X -> X -> Type v}
      -> Spine H (S n) -> Spine H n
    spine-inner (s ⨾ _) = s

    -- Sub-coherences extracted from coh₃ via spine-inner
    coh₂ : segal (∂ flast τ) ≡ [ _ ] ⨾ f ⨾ g
    coh₂ = ap spine-inner coh₃

    coh₁ : segal (∂ flast (∂ flast τ)) ≡ [ _ ] ⨾ f
    coh₁ = ap spine-inner coh₂

    -- Edge cell extractions from segal counit.
    -- For a Spine (S n), (edge fzero s) .fst is the outermost
    -- edge's underlying Cell 1.
    edge-g : ∂ fzero (∂ flast τ) ≡ g .fst
    edge-g = ap (λ s -> (edge fzero s) .fst) coh₂

    edge-h : ∂ fzero (∂ fzero τ) ≡ h .fst
    edge-h = ap (λ s -> (edge fzero s) .fst) coh₃

    -- Vertex extraction from coh₃
    vtx-w : vertex fzero (segal τ) ≡ w
    vtx-w = ap (vertex fzero) coh₃

    -- Build segal (e .fst) ≡ [ tgt ] ⨾ e for a 1-cell e.
    -- Following the pattern of inner-spine-eq in idl.
    segal-1-cell
      : ∀ {a b} (e : 1-Cell a b)
      -> segal (e .fst) ≡ [ b ] ⨾ e
    segal-1-cell (c , src , tgt) =
      ap [_] tgt
      ⨾ₚ src
      /ₚ 1-cell-pathp {p = src} {q = tgt} refl

    -- face-face instances on τ (at n = S Z, i j : Fin 3)
    --
    -- face-face: ∂ i (∂ (fsuc j) x) ≡ ∂ j (∂ (weaken i) x)
    --            when lower i ≤ lower j

    -- #6: i=flast j=flast: ∂ flast (∂ flast τ) ≡ ∂ flast face₂τ
    ff-ll : ∂ flast (∂ flast τ) ≡ ∂ flast face₂τ
    ff-ll = face-face {n = S Z} {i = flast} {j = flast}
              Nat.le.rx

    -- #3: i=fzero j=flast: ∂ fzero (∂ flast τ) ≡ ∂ flast (∂ fzero τ)
    ff-0l : ∂ fzero (∂ flast τ) ≡ ∂ flast (∂ fzero τ)
    ff-0l = face-face {n = S Z} {i = fzero} {j = flast}
              Nat.lt.z<s

    -- #2: i=fzero j=∂₁₂: ∂ fzero face₂τ ≡ ∂ ∂₁₂ (∂ fzero τ)
    ff-01 : ∂ fzero face₂τ ≡ ∂ ∂₁₂ (∂ fzero τ)
    ff-01 = face-face {n = S Z} {i = fzero} {j = ∂₁₂}
              Nat.lt.z<s

    -- #5: i=∂₁₂ j=flast: ∂ ∂₁₂ (∂ flast τ) ≡ ∂ flast face₁τ
    ff-1l : ∂ ∂₁₂ (∂ flast τ) ≡ ∂ flast face₁τ
    ff-1l = face-face {n = S Z} {i = ∂₁₂} {j = flast}
              (step suc)

    -- #1: i=fzero j=fzero: ∂ fzero face₁τ ≡ ∂ fzero (∂ fzero τ)
    ff-00 : ∂ fzero face₁τ ≡ ∂ fzero (∂ fzero τ)
    ff-00 = face-face {n = S Z} {i = fzero} {j = fzero}
              Nat.le.rx

    -- face-face on ∂ fzero τ : Cell 2 (at n = Z)
    -- i=fzero j=fzero: ∂ fzero (∂ ∂₁₂ (∂ fzero τ)) ≡ ∂ fzero (∂ fzero (∂ fzero τ))
    ff-00' : ∂ fzero (∂ ∂₁₂ (∂ fzero τ))
           ≡ ∂ fzero (∂ fzero (∂ fzero τ))
    ff-00' = face-face {n = Z} {i = fzero} {j = fzero}
               {x = ∂ fzero τ} Nat.le.rx

    -- Spine equality for ∂ fzero τ : segal (∂ fzero τ) ≡ spine-gh.
    -- Inner: segal (∂ flast (∂ fzero τ)) ≡ [ _ ] ⨾ g
    -- Outer edge cell: ∂ fzero (∂ fzero τ) ≡ h .fst
    -- Source vertex: vertex fzero (segal (∂ fzero τ)) ≡ w
    gh-inner : segal (∂ flast (∂ fzero τ)) ≡ [ _ ] ⨾ g
    gh-inner =
      ap segal (sym ff-0l ∙ edge-g) ∙ segal-1-cell g

    gh-src : ∂ fzero (∂ fzero (∂ fzero τ)) ≡ w
    gh-src = vtx-w

    gh-spine : segal (∂ fzero τ) ≡ spine-gh
    gh-spine =
      gh-inner
      ⨾ₚ gh-src
      /ₚ 1-cell-pathp edge-h

    face₀-eq : ∂ fzero τ ≡ cell-gh
    face₀-eq =
      segal-cancel (gh-spine ∙ sym coh-gh)

    -- Spine equality for ∂ flast τ : segal (∂ flast τ) ≡ spine-fg.
    -- This is just coh₂ since coh₂ : segal (∂ flast τ) ≡ [ _ ] ⨾ f ⨾ g.
    fg-spine : segal (∂ flast τ) ≡ spine-fg
    fg-spine = coh₂

    face-last-eq : ∂ flast τ ≡ cell-fg
    face-last-eq =
      segal-cancel (fg-spine ∙ sym coh-fg)

    -- spine-eq-A: segal face₂τ ≡ spine-l = [ _ ] ⨾ f ⨾ (g ∘ h)
    --
    -- Inner: segal (∂ flast face₂τ) ≡ [ _ ] ⨾ f
    -- via ff-ll: ∂ flast (∂ flast τ) ≡ ∂ flast face₂τ
    -- and coh₁: segal (∂ flast (∂ flast τ)) ≡ [ _ ] ⨾ f

    inner-A : segal (∂ flast face₂τ) ≡ [ _ ] ⨾ f
    inner-A = ap segal (sym ff-ll) ∙ coh₁

    -- Outer edge cell: ∂ fzero face₂τ ≡ (g ∘ h) .fst
    -- via ff-01: ∂ fzero face₂τ ≡ ∂ ∂₁₂ (∂ fzero τ)
    -- and face₀-eq: ∂ fzero τ ≡ cell-gh
    edge-A : ∂ fzero face₂τ ≡ (g ∘ h) .fst
    edge-A = ff-01 ∙ ap (∂ ∂₁₂) face₀-eq

    -- Source vertex
    src-A : ∂ fzero (∂ fzero face₂τ) ≡ w
    src-A =
      ap (∂ fzero) ff-01
      ∙ ff-00'
      ∙ vtx-w

    spine-eq-A : segal face₂τ ≡ spine-l
    spine-eq-A =
      inner-A
      ⨾ₚ src-A
      /ₚ 1-cell-pathp edge-A

    -- spine-eq-B: segal face₁τ ≡ spine-r = [ _ ] ⨾ (f ∘ g) ⨾ h
    --
    -- Inner: segal (∂ flast face₁τ) ≡ [ _ ] ⨾ (f ∘ g)
    -- via ff-1l: ∂ ∂₁₂ (∂ flast τ) ≡ ∂ flast face₁τ
    -- and face-last-eq: ∂ flast τ ≡ cell-fg

    inner-B : segal (∂ flast face₁τ) ≡ [ _ ] ⨾ (f ∘ g)
    inner-B =
      ap segal (sym ff-1l ∙ ap (∂ ∂₁₂) face-last-eq)
      ∙ segal-1-cell (f ∘ g)

    -- Outer edge cell: ∂ fzero face₁τ ≡ h .fst
    -- via ff-00: ∂ fzero face₁τ ≡ ∂ fzero (∂ fzero τ)
    -- and edge-h: ∂ fzero (∂ fzero τ) ≡ h .fst
    edge-B : ∂ fzero face₁τ ≡ h .fst
    edge-B = ff-00 ∙ edge-h

    -- Source vertex
    src-B : ∂ fzero (∂ fzero face₁τ) ≡ w
    src-B =
      ap (∂ fzero) ff-00
      ∙ ap (∂ fzero) edge-h
      ∙ h .snd .fst

    spine-eq-B : segal face₁τ ≡ spine-r
    spine-eq-B =
      inner-B
      ⨾ₚ src-B
      /ₚ 1-cell-pathp edge-B

    path-A : face₂τ ≡ cell-l
    path-A = segal-cancel (spine-eq-A ∙ sym (segal-equiv.counit 2 spine-l))

    path-B : face₁τ ≡ cell-r
    path-B = segal-cancel (spine-eq-B ∙ sym (segal-equiv.counit 2 spine-r))

    cell-path : ∂ ∂₁₂ cell-l ≡ ∂ ∂₁₂ cell-r
    cell-path = sym (ap (∂ ∂₁₂) path-A) ∙ ff ∙ ap (∂ ∂₁₂) path-B

```

### Segal category

The Segal condition gives rise to a wild category. Since
kitcat's `Cat` uses diagrammatic composition `_⨾_` (f then g)
while our `_∘_` is reverse composition (f after g), we swap the
argument order.

For `is-unital`, we need:
- `is-eqv idn`: pre/post-composition with idn are equivalences,
  which follows from `idl`/`idr`.
- Idempotence: `idn ≡ idn ∘ idn`, which is `sym (idl idn)`.

```agda

  segal-cat : precategory u u
  segal-cat .precategory.ob            = Ob
  segal-cat .precategory.hom           = 1-Cell
  segal-cat .precategory._⨾_ f g      = g ∘ f
  segal-cat .precategory.unital x .fst = idn
  segal-cat .precategory.unital x .snd .fst .fst =
    (iso→equiv (λ g → g ∘ idn) id idr idr) .snd
  segal-cat .precategory.unital x .snd .fst .snd =
    (iso→equiv (λ g → idn ∘ g) id idl idl) .snd
  segal-cat .precategory.unital x .snd .snd = sym (idl idn)
  segal-cat .precategory.assoc f g h   = sym (assoc h g f)

{-# INLINE Segal.constructor #-}

```
