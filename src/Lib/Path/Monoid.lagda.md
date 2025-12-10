Lane Biocini
October 23, 2025

Some debt is owed to the fantastic erased cubical development related to
"Compiling Programs with Erased Univalence" by Nils Anders Danielsson,
located (here)[https://www.cse.chalmers.se/~nad/listings/dependent-lenses/README.Compiling-Programs-with-Erased-Univalence.html].

Where I built upon this was my realization that we could build an unbiased
composition operator in cubical by computing a path between a left-biased
and right-biased composition operator, and then defining our canonical
composite as a diagonal over a path `composite p q : catl p q ≡ catr p q`,
where we can then define `cat p q i = composite p q (~ i) i : A`,
which ends up yielding great behavior for consistent and principled
derivation of all the Groupoid laws - all groupoid lemmas systematically
use our conn lemma generating squares of the form `Square p p q q`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Path.Monoid where

open import Lib.Type
open import Lib.Cubical.Base
open import Lib.Cubical.Kan hiding (fill)
open import Lib.Path
open import Lib.Path.Gpd renaming (cat to infixr 40 _∙_)
open import Lib.Sigma
open import Lib.Pointed
open Lib.Path.Gpd.cat

private variable
  u v : Level
  A : Type u

-- module Magma (F : Type u → Type u) (G : A → A → F A → Type v)
--   (cons : ∀ x y (ws : F A) → G x y ws)
--   (e : ∀ x ws → G x x ws)
--   (yank : ∀ x ws → cons x x ws ≡ e x ws)
--   where

hcat2 : {A : Type u} {x y z : A}
      → {p q : x ≡ y} {r s : y ≡ z}
      → p ≡ q → r ≡ s → p ∙ r ≡ q ∙ s
hcat2 α β i = α i ∙ β i

hpaste : {A : Type u} {a0 a1 b0 b1 : A}
       → {a01 : a0 ≡ a1} {ab0 : a0 ≡ b0} {b01 : b0 ≡ b1} {ab1 : a1 ≡ b1}
       → Square a01 ab0 b01 ab1
       → {c0 c1 : A} {bc0 : b0 ≡ c0} {bc1 : b1 ≡ c1} {c01 : c0 ≡ c1}
       → Square b01 bc0 c01 bc1
       → Square a01 (ab0 ∙ bc0) c01 (ab1 ∙ bc1)
hpaste {a01} {ab0} α {bc0} β i j = hcomp (∂ i ∨ ~ j) λ where
  k (i = i0) → a01 j
  k (i = i1) → β k j
  k (j = i0) → fill ab0 bc0 i k
  k (k = i0) → α i j

vpaste : {A : I → Type u} {a0 b0 c0 : A i0} {a1 b1 c1 : A i1}
       → {a01 : a0 ≡ a1 :: A} {ab0 : a0 ≡ b0} {b01 : b0 ≡ b1 :: A} {ab1 : a1 ≡ b1}
       → Square ab0 a01 ab1 b01
       → {bc0 : b0 ≡ c0} {bc1 : b1 ≡ c1} {c01 : c0 ≡ c1 :: A}
       → Square bc0 b01 bc1 c01
       → Square (ab0 ∙ bc0) a01 (ab1 ∙ bc1) c01
vpaste {a01} {ab0} α {bc0} {c01} β i j =
  hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → a01 i -- α i (~ k)
    k (j = i1) → β i k -- c01 i
    k (i = i0) → fill ab0 bc0 j k -- cfill ab0 bc0 j (~ k)
    k (k = i0) → α i j -- β i j

```
module EH where

  module _ {A : Type u} {a b : A} {p q : a ≡ b} (α : p ≡ q) where
    ulnat : Square (unitl p) (lwhisker rfl α) (unitl q) α
    ulnat i = hcomp (∂ i) λ where
      k (i = i0) → unitl p
      k (i = i1) → unitl q
      k (k = i0) → {!!}
      

    urnat : Square (unitr p) (rwhisker rfl α) (unitr q) α
    urnat = {!!}

  module _ (A : Pt u)  where
    private b = A .snd

ybe : {A : Type u} {w x y z : A}
    → (p : w ≡ x) (q : w ≡ y) (r : y ≡ z) (s : x ≡ z)
    → p ∙ s ≡ q ∙ r
ybe {w} {x} {y} {z} p q r s i j = hcomp (∂ j ∨ ~ i) λ where
  k (j = i0) → H' i (~ k)
  k (i = i0) → fill p s j k
  k (j = i1) → s (i ∨ k)
  k (k = i0) → K i j where
    a0 : x ≡ y
    a0 = s ∙ hsym r

    a1 : x ≡ y
    a1 = hsym p ∙ q

    x0 : x ≡ x
    x0 = (s ∙ hsym r) ∙ hsym (hsym p ∙ q)

    y0 : y ≡ y
    y0 = hsym (hsym p ∙ q) ∙ (s ∙ hsym r)

    zw0 : z ≡ w
    zw0 = hsym s ∙ hsym p

    zw1 : z ≡ w
    zw1 = hsym r ∙ hsym q

    zy : z ≡ y
    zy = hsym r

    s0 : Square ((s ∙ hsym r) ∙ hsym (hsym p ∙ q)) (hsym p) p rfl
    s0 i j = paste p {!? ∙ ?!} q {!!} (λ i j → {!!}) j i

    u0 : Square (hsym s) (hsym s ∙ hsym p) p ((s ∙ hsym r) ∙ hsym (hsym p ∙ q))
    u0 = paste x0 p (hsym p) s0 (fill (hsym s) (hsym p))

    v0 : Square (hsym r) (hsym r) rfl (hsym (hsym p ∙ q) ∙ s ∙ hsym r)
    v0 = paste {!!} {!!} {!!} {!!} {!!}

    k0 : Square (hsym s ∙ hsym p) rfl (hsym r) q
    k0 = {!!}

    abx : Square x0 a0 y0 a1
    abx i j = hcomp (∂ i ∨ ~ j) λ where
      k (i = i0) → u0 j k
      k (i = i1) → v0 j k
      k (j = i0) → fill s (hsym r) i k
      k (k = i0) → {!!}

    -- aa : a0 ≡ a1
    -- aa = commutes2 s (hsym r) (hsym p) q {!λ i j → abx!}

    a : x ≡ y
    a i = abx i i

    composite : x ≡ y
    composite = hsym p ∙ q

    H : Square p rfl q composite
    H = fill (hsym p) q

    -- K' : Square rfl composite r s
    -- K' i j = hcomp (∂ i ∨ j) λ where
    --   k (i = i0) → {!!}
    --   k (i = i1) → r j
    --   k (j = i1) → s (i ∨ ~ k)
    --   k (k = i0) → {!q (i ∨ j)!}

    H' : Square p rfl q a
    H' i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → i=i0 j k
      k (i = i1) → {!!}
      k (j = i0) → {!cfill s (hsym r)!}
      k (j = i1) → {!!}
      k (k = i0) → abx i j
        where
          i=i0 : Square (hsym p) x0 rfl p
          i=i0 = {!!}

    K : Square rfl a r s
    K i j = hcomp (∂ i ∨ j) λ where
      k (i = i0) → s (~ k)
      k (i = i1) → r j
      k (j = i1) → s (i ∨ ~ k)
      k (k = i0) → r (j ∨ ~ i)
