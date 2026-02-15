Lane Biocini
February 2025

Wild isomorphisms

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Magmoid.Type
import Cat.Magmoid.Data.Neutral as N
import Cat.Magmoid.Data.Unit as U

module Cat.Magmoid.Data.Iso (M : Magmoids) (u : ∀ x → N.unital M x) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan using (pcom; _∙_)
open import Core.Transport
open import Core.Equiv hiding (_≃_)

open import Cat.Magmoid.Data.Base M
open N M

private module unit {x} = U M (u x)
open unit

module _ {x y} (f : hom x y) where
  left-inverse : hom y x → Type h
  left-inverse g = f ⨾ g ≡ idn

  right-inverse : hom y x → Type h
  right-inverse h = h ⨾ f ≡ idn

  is-iso : Type h
  is-iso = Σ g ∶ hom y x , left-inverse g × right-inverse g

_≅_ : ob → ob → Type h
x ≅ y = Σ f ∶ hom x y , is-iso f
infix 4 _≅_

idn-iso : ∀ x → is-iso (idn {x})
idn-iso x = idn , unitl idn , unitr idn

iso-refl : ∀ {x} → x ≅ x
iso-refl {x} = idn , idn-iso x

iso-sym : ∀ {x y} → x ≅ y → y ≅ x
iso-sym (f , g , p , q) = g , f , q , p

module iso-coh (assoc : associativity) where
  iso-cat : ∀ {x y z} → x ≅ y → y ≅ z → x ≅ z
  iso-cat (f , g , p , q) (f' , g' , p' , q') = f ⨾ f'
    , g' ⨾ g
    , pcom (assoc f f' (g' ⨾ g))
           (f ◃ assoc f' g' g)
           (pcom (f ◃ (sym p' ▹ g)) (f ◃ unitl g) p)
    , pcom (assoc g' g (f ⨾ f'))
           (g' ◃ assoc g f f')
           (pcom (g' ◃ (sym q ▹ f')) (g' ◃ unitl f') q')

  module _ {x y} {f : hom x y} ((g , p , q) : is-iso f) where
    inv-unique
      : {s r : hom y x} → left-inverse f s → right-inverse f r → s ≡ r
    inv-unique {s} {r} p' q' =
      pcom (unitl s) (sym q' ▹ s)
        (pcom (assoc r f s) (r ◃ p') (unitr r))
