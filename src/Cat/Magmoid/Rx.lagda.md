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

module Cat.Magmoid.Rx (M : Magmoids) (u : ∀ x → M.unital M x) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv hiding (_≃_)

open import Cat.Magmoid.Base M
private module unit {x} = M.unital M (u x)
open unit renaming (unit to idn) public

module _  {x y} where
  sect : hom x y → Type h
  sect f = Σ s ∶ hom _ _ , f ⨾ s ≡ idn

  retr : hom x y → Type h
  retr f = Σ r ∶ hom _ _ , r ⨾ f ≡ idn

  is-biinv : hom x y → Type h
  is-biinv f = sect f × retr f

  is-neutral→is-biinv : {f : hom x y} → is-neutral f → is-biinv f
  is-neutral→is-biinv {f = f} p .fst .fst = Equiv.inv ((f ⨾_) , p .snd) idn
  is-neutral→is-biinv {f = f} p .fst .snd = Equiv.counit ((f ⨾_) , p .snd) idn
  is-neutral→is-biinv {f = f} p .snd .fst = Equiv.inv ((_⨾ f) , p .fst) idn
  is-neutral→is-biinv {f = f} p .snd .snd = Equiv.counit ((_⨾ f) , p .fst) idn

module wild-eqv (assoc : associativity) where
  _≃_ : ob → ob → Type h
  _≃_ x y = Σ f ∶ hom x y , is-biinv f

  module _ {x y} {f : hom x y} (((s , p) , (r , q)) : is-biinv f) where
    is-biinv→is-neutral : is-neutral f
    is-biinv→is-neutral  .fst .eqv-fibers h .center
      = h ⨾ r , pcom (assoc h r f) (ap (h ⨾_) q) (unitr h)
    is-biinv→is-neutral .fst .eqv-fibers h .paths (x0 , q0) i .fst
      = pcom {w = h ⨾ r} {z = x0} refl
          (sym (unitr (h ⨾ r)))
        (pcom
          (ap ((h ⨾ r) ⨾_) p)
          (assoc (h ⨾ r) f s)
        (pcom
          (ap (_⨾ s) (assoc h r f))
          (ap (λ k → (h ⨾ k) ⨾ s) q)
        (pcom
          (ap (_⨾ s) (sym (unitr h)))
          (ap (_⨾ s) (sym q0))
        (pcom
          (assoc x0 f s)
          (ap (x0 ⨾_) p)
          (unitr x0))))) i
    is-biinv→is-neutral .fst .eqv-fibers h .paths (x0 , q0) i .snd = {!!}
    is-biinv→is-neutral .snd .eqv-fibers h = {!!}

  -- id-sq : (f : hom x y) → commutative-sq f idn idn f
  -- id-sq f = unitl f ∙ sym (unitr f)
