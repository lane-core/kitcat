Lane Biocini
Oct 14th, 2024

When it came to doing this I was initially inspired by 1lab and TypeTopology,
but over the course of considering my approach I drew heavy inspiration from
Agda-Categories. My original motivation was to explore category theory
formalization with Petrakis' construction to consider hom-typoids instead of
hom-setoids. Petrakis develops a sophisticated apparatus in his Univalent
Typoids paper that is consistent with univalent treatments of type theory; it is
eminently adaptable towards doing category theory I wager.

```agda

{-# OPTIONS --safe #-}

module Cat.Base.Type where

open import Lib.Prim
open import Lib.Pi using (flip)
open import Lib.Product

open import Lib.Trait.Cut
open import Lib.Trait.Typoid.Type
open import Lib.Trait.Typoid.Base

record category u v w : (u ⊔ v ⊔ w) ⁺ type where
 infix 0 _≈_
 field
  ob : u type
  hom : ob → ob → v type
  idn : ∀ a → hom a a
  concat : ∀ {a b c} → hom a b → hom b c → hom a c

  _≈_ : ∀ {a b} → hom a b → hom a b → w type
  assoc : ∀ {a b c d} (f : hom a b) (g : hom b c) (h : hom c d)
        → concat (concat f g) h ≈ concat f (concat g h)
  idnl : ∀ {x y} (f : hom x y) → concat (idn x) f ≈ f
  idnr : ∀ {x y} (f : hom x y) → concat f (idn y) ≈ f
  hcomp : {a b c : ob} {f f' : hom a b} {g g' : hom b c}
        → f ≈ f' → g ≈ g' → concat f g ≈ concat f' g'

  -- Carette, when you're right you're right (see notes in:
  -- https://agda.github.io/agda-categories/Categories.Category.Core.html)
  idn-idn : ∀ x → concat (idn x) (idn x) ≈ idn x
  assoc-inv : ∀ {a b c d} (f : hom c d) (g : hom b c) (h : hom a b)
            → concat h (concat g f) ≈ concat (concat h g) f

  _≋_ : ∀ {a b} {f g : hom a b} → f ≈ g → f ≈ g → w type
  has-typd : (a b : ob) → has-typoid (_≈_ {a} {b}) (_≋_ {a} {b})

 hom-typoid : (a b : ob) → Typoid v w w
 hom-typoid a b .fst = hom a b
 hom-typoid a b .snd = record { _≃_ = _≈_ ; _≅_ = _≋_ ; has-typd = has-typd a b }

 private module hom {a b : ob} = Typoid (hom-typoid a b)

 instance
  hom-cut : {y z : ob} → Cut ob (λ x → hom x y) (λ x _ → hom y z → hom x z)
  hom-cut .seq = concat

 _◁_ : ∀ {a b c} (f : hom a b) {g h : hom b c} → g ≈ h → f ∙ g ≈ f ∙ h
 _◁_ f H = hcomp (hom.eqv f) H

 _▷_ : ∀ {a b c} {f g : hom a b} → f ≈ g → (h : hom b c) → f ∙ h ≈ g ∙ h
 _▷_ K h = hcomp K (hom.eqv h)

 op : category u v w
 op .ob = ob
 op .hom = flip hom
 op .idn = idn
 op .concat = flip concat
 op ._≈_ = _≈_
 op .assoc = assoc-inv
 op .idnl = idnr
 op .idnr = idnl
 op .hcomp = flip hcomp
 op .idn-idn = idn-idn
 op .assoc-inv = assoc
 op ._≋_ = _≋_
 op .has-typd = flip has-typd

private module _ {u v w} (C : category u v w) where
 open import Lib.Path
 private module C = category C

 op-op : category.op C.op ≡ C
 op-op = path (category.op C.op)
