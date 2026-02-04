Surjections: maps with merely inhabited fibers.

A map `f : A → B` is surjective if every element of B has a preimage, at
least in the sense that the fiber is merely inhabited. This is weaker than
having a section (split surjectivity), which would require an actual choice
of preimage.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Function.Surjection where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Trunc
open Trunc
open import Core.Equiv
open import Core.Function.Embedding
open import Core.HLevel
open import Core.Transport.Properties using (prop-inhabited→is-contr)

private variable
  u v : Level
  A B : Type u
```


## Core Definitions

```agda

-- A map is surjective if all fibers are merely inhabited
is-surjective : {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
is-surjective f = ∀ b → ∥ fiber f b ∥

-- Bundled surjection
_↠_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ↠ B = Σ f ∶ (A → B) , is-surjective f
infix 6 _↠_

-- Split surjection (has a section, i.e., actual choice of preimages)
is-split-surjective : {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
is-split-surjective f = ∀ b → fiber f b
```


## Conversions

```agda

-- Equivalences are surjective (fibers are contractible, hence inhabited)
equiv→surjective
  : {A : Type u} {B : Type v} {f : A → B}
  → is-equiv f → is-surjective f
equiv→surjective e b = ∣ e .eqv-fibers b .center ∣

-- Split surjective implies surjective
split-surjective→surjective
  : {A : Type u} {B : Type v} {f : A → B}
  → is-split-surjective f → is-surjective f
split-surjective→surjective split b = ∣ split b ∣

-- Surjective + embedding = equivalence
-- Key insight: if f is an embedding, fibers are props.
-- If f is surjective, fibers are merely inhabited.
-- Merely inhabited prop = contractible.
surjective+embedding→equiv
  : {A : Type u} {B : Type v} {f : A → B}
  → is-surjective f → is-embedding f → is-equiv f
surjective+embedding→equiv {f = f} surj emb .eqv-fibers b =
  prop-inhabited→is-contr (emb b) (out (emb b) (surj b))
```
