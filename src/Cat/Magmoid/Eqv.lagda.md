Lane Biocini
February 2025

Magmoids and the structures we can characterize within them.

We compile all the definitions into a module meant to instantiate uniform definitions
for any category-like (i.e. magmoidal) structure; we also even have the machinery
for heteromorphisms between structures that only agree in being magmoidal,
see the definitions for functor, adjunctions, nat-trans, etc.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Magmoid.Type
import Cat.Magmoid.Base as M

module Cat.Magmoid.Eqv (M : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

open M M

comp-is-eqv
  : ∀ {a b c} {f : hom a b} {g : hom b c}
  → is-eqv f → is-eqv g → is-eqv (_⨾_ f g)
comp-is-eqv {f} {g} fe ge .fst =
  subst is-equiv (funext (λ h → sym (assoc h f g)))
    (_∙e_ (_⨾ f , fe .fst) (_⨾ g , ge .fst) .snd)
comp-is-eqv {f} {g} fe ge .snd =
  subst is-equiv (funext λ h → assoc f g h)
    (_∙e_ (g ⨾_ , ge .snd) (f ⨾_ , fe .snd) .snd)

iso-cat :  ∀ {a b c} → a ≅ b → b ≅ c → a ≅ c
iso-cat e d .fst = e .fst ⨾ d .fst
iso-cat e d .snd = comp-is-eqv (e .snd) (d .snd)

module _ {a b} ((e , divl , divr) : a ≅ b) where
  private
    module e = iso (divl , divr)

    c0 : hom b b
    c0 = eqv-fibers divr e .center .fst

    c1 : hom b a
    c1 = eqv-fibers divl c0 .center .fst

    p0 : e ⨾ c0 ≡ e
    p0 = eqv-fibers divr e .center .snd

    p1 : c1 ⨾ e ≡ c0
    p1 = eqv-fibers divl c0 .center .snd

    e0 : ∀ {w} → is-equiv (λ (k : hom w b) → k ⨾ c0)
    e0 {w}
      = 3-for-2-right {f = λ (k : hom w a) → k ⨾ e} {g = λ (k : hom w b) → k ⨾ c0} divl
          (subst is-equiv (funext λ k → ap (k ⨾_) (sym p0) ∙ assoc k e c0) divl)

    e1 : ∀ {z} → is-equiv (λ (g : hom b z) → c0 ⨾ g)
    e1 {z}
      = 3-for-2-left {f = λ (g : hom b z) → c0 ⨾ g} {g = λ (g : hom b z) → e ⨾ g} divr
          (subst is-equiv (funext λ g → sym (assoc e c0 g ∙ ap (_⨾ g) p0)) divr)

  iso-sym : b ≅ a
  iso-sym .fst = c1
  iso-sym .snd .fst {w} =
    3-for-2-left {f = λ (k : hom w b) → k ⨾ c1} {g = λ (k : hom w a) → k ⨾ e} divl
      (subst is-equiv (funext λ k → ap (k ⨾_) (sym p1) ∙ assoc k c1 e) e0)
  iso-sym .snd .snd {z} =
    3-for-2-right {f = λ (g : hom b z) → e ⨾ g} {g = λ (g : hom a z) → c1 ⨾ g} divr
      (subst is-equiv (funext λ g₀ → ap (_⨾ g₀) (sym p1) ∙ sym (assoc c1 e g₀)) e1)

has-pentagon : Type (o ⊔ h)
has-pentagon
  = ∀ {w x y z a} (f : hom w x) (g : hom x y) (k : hom y z) (l : hom z a)
  → pentagon f g k l (assoc g k l) (assoc f (g ⨾ k) l) (assoc f g k)
             (assoc f g (k ⨾ l)) (assoc (f ⨾ g) k l)

module 2-cat (units : ∀ x → unital x) where
  has-triangle : Type (o ⊔ h)
  has-triangle
    = ∀ {x y z} (f : hom x y) (g : hom y z) → triangle f g (units y) (assoc f (units y .fst) g)

  record is-2-coherent : Type (o ⊔ h) where
    no-eta-equality
    field
      tri : has-triangle
      pen : has-pentagon
