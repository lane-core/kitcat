Lane Biocini
October 23, 2025

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Equiv where

open import Lib.Type
open import Lib.Sigma
open import Lib.Cubical.Base
open import Lib.Cubical.Kan hiding (fill)
open import Lib.Path
open import Lib.Path.HLevel
open import Lib.Cubical.Sub

private variable
  u v : Level
  A : I → Type u

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    contr : (y : B) → is-contr (fiber f y)

  fun = f

  center : (y : B) → fiber f y
  center y = contr y .ctr

  inv : B → A
  inv y = center y .fst

  fibers : {y : B} (fb : fiber f y) → center y ≡ fb
  fibers {y} = contr y .paths

  sec : (x : A) → inv (f x) ≡ x
  sec x i = fibers (x , rfl) i .fst

  retr :  (y : B) → f (inv y) ≡ y
  retr y = center y .snd

_≃_ Equiv : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ {A = A → B} is-equiv
Equiv = _≃_
{-# BUILTIN EQUIV _≃_ #-}

eqvtofun : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqvtofun e = fst e
{-# BUILTIN EQUIVFUN eqvtofun #-}

equiv-proof : ∀ {u v} (T : Type u) (A : Type v) (w : T ≃ A) (a : A)
            → ∀ φ (u : Partial φ (fiber (w .fst) a)) → fiber (w .fst) a [ φ ↦ u ]
equiv-proof {u} {v} T A w a = is-contr→extend (is-equiv.contr (w .snd) a)
{-# BUILTIN EQUIVPROOF equiv-proof #-}
