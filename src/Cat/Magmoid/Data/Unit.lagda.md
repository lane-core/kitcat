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
import Cat.Magmoid.Data.Base as B
import Cat.Magmoid.Data.Neutral as N

module Cat.Magmoid.Data.Unit (M : Magmoids) {x} (u : N.unital M x) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv hiding (_≃_)

open Sigma u renaming (fst to i; snd to e)

open B M
open N M

open is-neutral (e .N.is-unital.neutral)
open is-unital e renaming (neutral to neu)

idn : hom x x
idn = i

unitl : ∀ {y} (f : hom x y) → i ⨾ f ≡ f
unitl {y} f = pcom (pre-unit (i ⨾ f)) (ap divl (lcoh f)) (pre-unit f)

unitr : ∀ {w} (f : hom w x) → f ⨾ i ≡ f
unitr {w} f = pcom (post-unit (f ⨾ i)) (ap divr (rcoh f)) (post-unit f)

idem : i ⨾ i ≡ i
idem j = cone (unitl i) (unitr i) j j

neutral : is-neutral i
neutral = neu

f0 : Path (fiber (_⨾ i) i) (coloop , post-counit i) (i , idem)
f0 = Equiv.fibers ((_⨾ i) , neutral .fst) (i , idem)

f1 : Path (fiber (i ⨾_) i) (loop , pre-counit i) (i , idem)
f1 = Equiv.fibers ((i ⨾_) , neutral .snd) (i , idem)

coloop-coh : coloop ≡ i
coloop-coh = ap fst f0

loop-coh : loop ≡ i
loop-coh = ap fst f1

unit-thunkable : is-thunkable i
unit-thunkable g h = unitl (g ⨾ h) ∙ sym (unitl g ▹ h)

unit-linear : is-linear i
unit-linear f g = (f ◃ unitr g) ∙ sym (unitr (f ⨾ g))

coloop-absorb
  : ∀ {y} {f : hom x y} (fn : is-neutral f)
  → is-neutral.coloop fn ≡ i
coloop-absorb fn =
  ap fst (Equiv.fibers ((_⨾ _) , fn .fst) (i , unitl _))

loop-absorb
  : ∀ {w} {d : hom w x} (dn : is-neutral d)
  → is-neutral.loop dn ≡ i
loop-absorb dn =
  ap fst (Equiv.fibers ((_ ⨾_) , dn .snd) (i , unitr _))

absorb-unital : ∀ {j : hom x x} → j ≡ i → is-unital j
absorb-unital {j} p .is-unital.neutral =
  coe10 (λ k → is-neutral (p k)) neutral
absorb-unital {j} p .is-unital.lcoh f =
  (p ▹ (j ⨾ f)) ∙ pcom
    (i ◃ (sym p ▹ f))
    (lcoh f)
    (sym p ▹ f)
absorb-unital {j} p .is-unital.rcoh f =
  ((f ◃ p) ▹ j) ∙ pcom
    ((f ⨾ i) ◃ sym p)
    (rcoh f)
    (f ◃ sym p)

loop-unital : is-unital loop
loop-unital = absorb-unital loop-coh

coloop-unital : is-unital coloop
coloop-unital = absorb-unital coloop-coh

absorb-thunkable : ∀ {j : hom x x} → j ≡ i → is-thunkable j
absorb-thunkable p g h =
  (p ▹ (g ⨾ h)) ∙ unit-thunkable g h ∙ sym ((p ▹ g) ▹ h)

absorb-linear : ∀ {j : hom x x} → j ≡ i → is-linear j
absorb-linear p f g =
  (f ◃ (g ◃ p)) ∙ unit-linear f g ∙ sym ((f ⨾ g) ◃ p)

loop-thunkable : is-thunkable loop
loop-thunkable = absorb-thunkable loop-coh

loop-linear : is-linear loop
loop-linear = absorb-linear loop-coh

loop-absorb-unital
  : ∀ {w} {d : hom w x} (dn : is-neutral d)
  → is-unital (is-neutral.loop dn)
loop-absorb-unital dn = absorb-unital (loop-absorb dn)

coloop-absorb-unital
  : ∀ {y} {f : hom x y} (fn : is-neutral f)
  → is-unital (is-neutral.coloop fn)
coloop-absorb-unital fn = absorb-unital (coloop-absorb fn)

coloop-thunkable : is-thunkable coloop
coloop-thunkable = absorb-thunkable coloop-coh

coloop-linear : is-linear coloop
coloop-linear = absorb-linear coloop-coh

loop-absorb-thunkable
  : ∀ {w} {d : hom w x} (dn : is-neutral d)
  → is-thunkable (is-neutral.loop dn)
loop-absorb-thunkable dn = absorb-thunkable (loop-absorb dn)

loop-absorb-linear
  : ∀ {w} {d : hom w x} (dn : is-neutral d)
  → is-linear (is-neutral.loop dn)
loop-absorb-linear dn = absorb-linear (loop-absorb dn)

coloop-absorb-thunkable
  : ∀ {y} {f : hom x y} (fn : is-neutral f)
  → is-thunkable (is-neutral.coloop fn)
coloop-absorb-thunkable fn = absorb-thunkable (coloop-absorb fn)

coloop-absorb-linear
  : ∀ {y} {f : hom x y} (fn : is-neutral f)
  → is-linear (is-neutral.coloop fn)
coloop-absorb-linear fn = absorb-linear (coloop-absorb fn)

divl-triv : ∀ {y} (g : hom x y) → divl g ≡ g
divl-triv g = sym (unitl (divl g)) ∙ pre-counit g

divr-triv : ∀ {w} (g : hom w x) → divr g ≡ g
divr-triv g = sym (unitr (divr g)) ∙ post-counit g

unique : ((j , d) : unital x) → i ≡ j
unique (j , d) = sym (unitr-j i) ∙ unitl j where
  open is-neutral (d .N.is-unital.neutral)
    renaming (post-unit to post-unit-j; divr to divr-j)
  unitr-j : ∀ {w} (f : hom w x) → f ⨾ j ≡ f
  unitr-j f = pcom (post-unit-j (f ⨾ j))
    (ap divr-j (N.is-unital.rcoh d f)) (post-unit-j f)

post≡pre : ∀ (f : hom x x) → f ⨾ i ≡ i ⨾ f
post≡pre f = unitr f ∙ sym (unitl f)

pre≡post : ∀ (f : hom x x) → i ⨾ f ≡ f ⨾ i
pre≡post f = unitl f ∙ sym (unitr f)

neutral-comm
  : PathP (λ j → is-equiv (λ (f : hom x x) → post≡pre f j))
          (neutral .fst) (neutral .snd)
neutral-comm = is-prop→PathP
  (λ j → is-equiv-is-prop _) (neutral .fst) (neutral .snd)

neutral-comm⁻¹
  : PathP (λ j → is-equiv (λ (f : hom x x) → pre≡post f j))
          (neutral .snd) (neutral .fst)
neutral-comm⁻¹ = is-prop→PathP
  (λ j → is-equiv-is-prop _) (neutral .snd) (neutral .fst)

triangle-coherator
  : ∀ {w y} (f : hom w x) (g : hom x y) → f ⨾ i ⨾ g ≡ (f ⨾ i) ⨾ g → Type h
triangle-coherator f g a0 = a0 ∙ (unitr f ▹ g) ≡ f ◃ (unitl g)
{-# INLINE triangle-coherator #-}

module eq-laws (assoc : associativity) where
  open associative assoc

  neu-unitl
    : ∀ {y} (e : x ≐ y)
    → neu-cat (neu-refl u) e ≡ e
  neu-unitl e j .fst = unitl (e .fst) j
  neu-unitl e j .snd = is-prop→PathP
    (λ j → is-neutral-is-prop (unitl (e .fst) j))
    (neu-cat (neu-refl u) e .snd) (e .snd) j

  neu-unitr
    : ∀ {y} (e : y ≐ x)
    → neu-cat e (neu-refl u) ≡ e
  neu-unitr e j .fst = unitr (e .fst) j
  neu-unitr e j .snd = is-prop→PathP
    (λ j → is-neutral-is-prop (unitr (e .fst) j))
    (neu-cat e (neu-refl u) .snd) (e .snd) j
