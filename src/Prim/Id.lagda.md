```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Prim.Id where

open import Prim.Type
open import Prim.Data.Sigma

open import Prim.Interval
open import Prim.Kan using (transp; hcomp; hfill; coe0i; coe01)

import Prim.Path as Path
open Path using (_≡_; PathP; is-contr; ctr; paths)

private variable
  u v : Level
  @0 A : Type u
  @0 B : Type v

PathP#0 : ∀ {u} (@0 A : I → Type u) → @0 A i0 → @0 A i1 → Type u
PathP#0 A x y = Erased (PathP A x y)

Id : ∀ {u} (@0 A : Type u) (@0 x y : A) → Type u
Id A x y = PathP#0 (λ _ → A) x y

_＝_ : ∀ {u} {@0 A : Type u} (@0 x y : A) → Type u
_＝_ {A = A} x y = PathP#0 (λ _ → A) x y
{-# DISPLAY Id _ = _＝_ #-}

refl : {@0 x : A} → x ＝ x
refl {x = x} .Erased.erased = λ _ → x

sym : {@0 x y : A} → x ＝ y → y ＝ x
sym (erase q) .erased = λ i → q (~ i)

concat : {@0 x y z : A} → x ＝ y → y ＝ z → x ＝ z
concat (erase p) (erase q) .erased = Path.concat p q

data Id-view {u} {@0 A : Type u} (@0 x : A) : ∀ {@0 y} → @0 x ＝ y → Type u where
  isRefl : Id-view x refl

＝view : ∀ {u} {@0 A : Type u} {@0 x y : A} (@0 q : x ＝ y) → Id-view x q
＝view {x = x} (erase q) = Path.J#0 (λ (@0 z) (s : x ≡ z) → Id-view x (erase s)) isRefl q

J : ∀ {u v} {@0 A : Type u} {x : A}
  → (P : ∀ y → x ＝ y → Type v)
  → P x refl → ∀ {y} (q : x ＝ y) → P y q
J P c q with (＝view q)
... | isRefl = c

-- ap : ∀ {u v} {A : Type u} {B : A → Type v}
--    → (f : ∀ x → B x) {x y : A}
--    → (p : x ＝ y)
--    →
-- ap f p i = f (p i)

-- J-refl : ∀ {u v} {A : Type u} {x : A}
--        → (P : ∀ y → x ＝ y → Type v)
--        → (c : P x refl)
--        → J P c refl ＝ c
-- J-refl {x = x} P c ._＝_.path i = Path.erased-J (λ y q → P y {!q!}) {!!} {!!}
```
erefl : (x : A) → x ＝ x
erefl x _ = x
{-# INLINE erefl #-}

sym : {u : P i0} {v : P i1} → PathP P u v → PathP (λ i → P (~ i)) v u
sym p i = p (~ i)
{-# INLINE sym #-}

actp : ∀ {u v} {A : I → Type u} {B : (i : I) → (A i) → Type v}
   → (f : ∀ (i : I) (a : A i) → B i a)
   → {x : A i0} {y : A i1} (p : PathP A x y)
   → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
actp f p i = f i (p i)
{-# INLINE actp #-}

syntax actp (λ i → f) p = ∂ i ↦ f $ p

ap : ∀ {u v} {A : Type u} {B : A → Type v}
   → (f : ∀ x → B x) {x y : A}
   → (p : x ＝ y)
   → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

tr : ∀ {u v} {A : Type u} (P : A → Type v)
   → {x y : A} (q : x ＝ y)
   → P x → P y
tr P {x} {y} q = coe01 (∂.line P q)

idtofun : ∀ {u} {A B : Type u} → A ＝ B → A → B
idtofun = tr id

J : ∀ {u v} {A : Type u} {x : A}
  → (P : ∀ y → x ＝ y → Type v)
  → P x refl → ∀ {y} (q : x ＝ y) → P y q
J P c q = coe01 (∂.square P q) c

{-# DISPLAY coe01 (∂.square P q) c = J P c q #-}
{-# DISPLAY coe01 (∂.line P q) = tr P q #-}
{-# DISPLAY tr id = idtofun #-}

module _ {u} {A : Type u} where
  concat : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  concat {x} p q i = hcomp (∂ i) sys
    module concat where
      sys : (j : I) → Partial (∂ i ∨ ~ j) A
      sys j (i = i0) = x
      sys j (j = i0) = p i
      sys j (i = i1) = q j

      fill : p i ＝ concat p q i
      fill j = hfill (∂ i) j sys

  filler : {x y z : A} (p : x ＝ y) (q : y ＝ z)
         → PathP (λ i → p i ＝ concat p q i) refl q
  filler p q i = concat.fill p q i

  lunit : {x y : A} (p : x ＝ y) → p ＝ concat refl p
  lunit {x} p i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → x
    k (i = i0) → p (j ∧ k)
    k (j = i1) → p k
    k (k = i0) → x

  runit : {x y : A} (p : x ＝ y) → p ＝ concat p refl
  runit p i j = concat.fill p refl j i

  rinv : {x y : A} (p : x ＝ y) → refl ＝ concat p (sym p)
  rinv {x} p i j = hcomp (∂ j ∨ ~ i) λ where
    k (i = i0) → x
    k (j = i0) → x
    k (j = i1) → p (i ∧ ~ k)
    k (k = i0) → p (i ∧ j)

  linv : {x y : A} (p : x ＝ y) → refl ＝ concat (sym p) p
  linv {y = y} p = rinv (sym p)

  assoc : {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
        → concat p (concat q r) ＝ concat (concat p q) r
  assoc {w} {z = z} p q r i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → w
    k (i = i1) → concat.fill (concat p q) r j k
    k (k = i0) → concat.fill p q j i
    k (j = i1) → hcomp (∂ k ∨ i) λ where
      l (i = i1) → r (k ∧ l)
      l (k = i0) → q i
      l (k = i1) → r l
      l (l = i0) → q (k ∨ i)

{-# DISPLAY hcomp _ (concat.sys p q _) = concat p q #-}
