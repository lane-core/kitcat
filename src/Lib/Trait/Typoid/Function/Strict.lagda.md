Lane Biocini
Oct 13th, 2024

Just some Strict Typoid fun.

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Function.Strict where

open import Lib.Prim
open import Lib.Data.Sigma using (Σ; fst; snd)
open import Lib.Pi.Base

open import Lib.Path.Type
open import Lib.Path.Base

open import Lib.Trait.Setoid
open import Lib.Trait.Typoid.Type
open import Lib.Trait.Typoid.Base using (Typoid)
open import Lib.Trait.Typoid.Equality
open import Lib.Trait.Typoid.Function.Type

module _ {u₁ v₁ w₁ u₂ v₂ w₂}
 (𝓐 : Typoid u₁ v₁ w₁)
 (𝓑 : Typoid u₂ v₂ w₂)
 where
 private
  module 𝓐 = Typoid 𝓐
  module 𝓑 = Typoid 𝓑

 record is-strict-typoid-fun (f : 𝓐.ob → 𝓑.ob) : u₁ ⊔ v₁ ⊔ w₁ ⊔ v₂ ⊔ w₂ type
  where
  field
   is-typd-fun : is-typoid-function 𝓐 𝓑 f

  open is-typoid-function is-typd-fun public
  open Σ has-associate renaming (fst to ϕ; snd to ϕ²)
  field
   is-strict : ∀ x → ϕ x x (𝓐.eqv x) ≡ 𝓑.eqv (f x)

module _ {u v w} (𝓐 : Typoid u v w) where
 open is-typoid-function
 open is-strict-typoid-fun
 private module 𝓐 = Typoid 𝓐
 private module 𝓐₀ = Typoid (Eq-Typoid 𝓐.ob)

 𝓐₀ : Typoid u u u
 𝓐₀ = Eq-Typoid 𝓐.ob

 idtoeqv : is-strict-typoid-fun 𝓐₀ 𝓐 id
 idtoeqv .is-typd-fun .has-associate .fst x y p = tr (x 𝓐.≃_) p (𝓐.eqv x)
 idtoeqv .is-typd-fun .has-associate .snd x y e d p =
  tr (λ u → tr (𝓐._≃_ x) e (𝓐.eqv x) 𝓐.≅ tr (𝓐._≃_ x) u (𝓐.eqv x))
     p (𝓐.eqv2 (tr (𝓐._≃_ x) e (𝓐.eqv x)))
 idtoeqv .is-typd-fun .associate-id x = 𝓐.eqv2 (𝓐.eqv (id x))
 idtoeqv .is-typd-fun .associate-comp {x} e₁ (path _) =
  𝓐.inv2 (𝓐.eqvr (tr (x 𝓐.≃_) e₁ (𝓐.eqv x)))
 idtoeqv .is-strict x = path (𝓐.eqv (id x))
