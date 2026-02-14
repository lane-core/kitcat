Lane Biocini
February 2025

Wild categories with quasi-unital identities.

In what follows we engages in a synthesis over the following
constructions, but guided along the lines of Chen's "2-Coherent
Internal Models of Homotopical Type Theory" as well as
Capirotti-Kraus' work. The idea is we define a notion of identity that
is a *characterization* of the sort of data that satisfies the
definition of a unital morphism, such that any other morphism
satisfying this characterization is provably identical to the
canonical one.

Implicitly this entails we shift our perspective with regard to
functors, natural transformations, and so on, where we eschew
laws applying to specific units and instead just ensure each
categorical construction respects isomorphisms.

References:
- John Chen, "Semicategories with Identities"
           & "2-Coherent Internal Models of Homotopical Type Theory"
- Capriotti-Kraus, "Univalent Higher Categories via Complete Semi-Segal Types"

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

open import Cat.Magmoid.Type
open import Cat.Magmoid.Base as Ax
import Cat.Magmoid.Interface as X

record precategory o h : Type₊ (o ⊔ h) where
  no-eta-equality
  infixr 40 _⨾_
  field
    ob  : Type o
    hom : ob → ob → Type h
    _⨾_ : ∀ {a b c} → hom a b → hom b c → hom a c
    assoc  : ∀ {a b c d} (f : hom a b) (g : hom b c) (h : hom c d)
           → f ⨾ (g ⨾ h) ≡ (f ⨾ g) ⨾ h
    units : ∀ x → Ax.unital (str ob hom _⨾_) x

{-# INLINE precategory.constructor #-}

private
  open magmoid-structure
  to-magmoid-str : ∀ o h → magmoid-structure ((o ⊔ h) ₊) o h
  to-magmoid-str o h .carrier = precategory o h
  to-magmoid-str o h .ob = precategory.ob
  to-magmoid-str o h .hom = precategory.hom
  to-magmoid-str o h .cut = precategory._⨾_

  module M = X to-magmoid-str
  module map {o o' h h'} (C : precategory o h) (D : precategory o' h') = M.map C D
  module nat {o o' h h'} {C : precategory o h} {D : precategory o' h'} = M.nat C D
  module het {o o' h h'} {C : precategory o h} {D : precategory o' h'} = M.het C D

open map public
open nat hiding (module coh) public
--open nat hiding (module coh) public
open het public

module Cat {o h} (C : precategory o h) where
  units = precategory.units C
  open M.base C public


  -- open C hiding (module morphism) public
  -- open C.morphism C public hiding (module reflexive; module coh)
  -- open C.morphism.reflexive C units public
  -- open C.morphism.coh C (C .precategory.assoc) public
