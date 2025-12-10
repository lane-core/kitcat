```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Data.Cat where

open import Lib.Type
open import Lib.Interval
open import Lib.Sigma
open import Lib.Path
open import Lib.Contr
open import Lib.Path.Gpd
open import Lib.Equiv

Mor : ∀ {u} v → Type u → Type (u ⊔ v ₊)
Mor v ob = ob → ob → Type v

record has-composites {u v} {A : Type u} (H : Mor v A) {x y} (f : H x y) : Type (u ⊔ v) where
  field
    pre : ∀ {w} → H w x → H w y
    post : ∀ {z} → H y z → H x z
    preCoh : ∀ {w} (f : H w y) → is-prop (fiber pre f)
    postCoh : ∀ {z} (g : H x z) → is-prop (fiber post g)

record is-iso {u v} {A : Type u} (H : Mor v A) {x y}
  {f : H x y} (cmp : has-composites H f) : Type (u ⊔ v)
  where
  private module cmp = has-composites cmp
  field
    pre : ∀ w → is-equiv (λ (h : H w x) → cmp.pre h)
    post : ∀ z → is-equiv (λ (g : H y z) → cmp.post g)

  unit : H x x
  unit = is-equiv.inv (pre x) f

  counit : H y y
  counit = is-equiv.inv (post y) f

record is-identity {u v} {A : Type u} (H : Mor v A) {x} {e : H x x} (cmp : has-composites H e) : Type (u ⊔ v) where
  private module cmp = has-composites cmp
  field
    preIdpt : ∀ {w} (h : H w x) → cmp.pre h ≡ h
    postIdpt : ∀ {z} (h : H x z) → cmp.post h ≡ h

  idpt : cmp.pre e ≡ cmp.post e
  idpt = Gpd.cat (preIdpt e) (hsym (postIdpt e))

  pre-eqv : ∀ w → is-equiv (λ (h : H w x) → cmp.pre h)
  pre-eqv w .is-equiv.contr y .ctr = y , preIdpt y
  pre-eqv w .is-equiv.contr y .paths = cmp.preCoh y (pre-eqv w .is-equiv.contr y .ctr)

  post-eqv : ∀ z → is-equiv (λ (h : H x z) → cmp.post h)
  post-eqv z .is-equiv.contr y .ctr = y , postIdpt y
  post-eqv z .is-equiv.contr y .paths = cmp.postCoh y (post-eqv z .is-equiv.contr y .ctr)

  iso : is-iso H cmp
  iso .is-iso.pre = pre-eqv
  iso .is-iso.post = post-eqv

record is-composable {u v} {A : Type u} (H : Mor v A) : Type (u ⊔ v) where
  field
    cmp : ∀ {x y} (f : H x y) → has-composites H f
  private module cmp {x y} (f : H x y) = has-composites (cmp f)
  field
    coh : ∀ {x y z} (f : H x y) (g : H y z) → (cmp.pre g) f ≡ (cmp.post f) g
    identity : ∀ {x} → Σ λ (e : H x x) → is-identity H (cmp e)

  open cmp using (pre; post) public

  idn : ∀ {x} → H x x
  idn = identity .fst

  cat : ∀ {x y z} → H x y → H y z → H x z
  cat f g = post f (pre idn g)

record Cat u v : Type₊ (u ⊔ v) where
  field
    Ob : Type u
    Hom : Ob → Ob → Type v
