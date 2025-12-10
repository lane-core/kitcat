```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Path.Erased where

open import Lib.Type
open import Lib.Erased
open import Lib.Sigma

open import Lib.Cubical.Base
open import Lib.Cubical.Kan using (transp; hcomp; hfill; coe0i; coe01)

open import Lib.Path using (J0; is-contr; ctr; paths)
open import Lib.Path.Gpd as Path

private variable
  u v : Level
  @0 A : Type u
  @0 B : Type v

PathP#0 : ∀ {u} (@0 A : I → Type u) → A i0 → A i1 → Type u
PathP#0 A x y = #0 (PathP A x y)

Id : ∀ {u} (@0 A : Type u) (x y : A) → Type u
Id A x y = PathP#0 (λ _ → A) x y

_＝_ : ∀ {u} {@0 A : Type u} (x y : A) → Type u
_＝_ {A = A} x y = PathP#0 (λ _ → A) x y
{-# DISPLAY Id _ = _＝_ #-}

refl : {@0 x : A} → x ＝ x
refl {x = x} .null = λ _ → x

sym : {@0 x y : A} → x ＝ y → y ＝ x
sym (void q) .null = λ i → q (~ i)

concat : {@0 x y z : A} → x ＝ y → y ＝ z → x ＝ z
concat (void p) (void q) .null = Path.cat p q

data Path-view {u} {@0 A : Type u} (@0 x : A) : ∀ {@0 y} → @0 x ＝ y → Type u where
  isRefl : Path-view x refl

＝view : ∀ {u} {@0 A : Type u} {@0 x y : A} (@0 q : x ＝ y) → Path-view x q
＝view {x = x} (void q) = J0 (λ (@0 z) (s : x ≡ z) → Path-view x (void s)) isRefl q

J#0 : ∀ {u v} {@0 A : Type u} {x : A}
    → (P : ∀ y → x ＝ y → Type v)
    → P x refl → ∀ {y} (q : x ＝ y) → P y q
J#0 P c q with (＝view q)
... | isRefl = c

