```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.HCompU where

open import Prim.Type
open import Prim.Interval
open import Prim.Sub
open import Prim.Kan
open import Prim.Path

open import Prim.Data.Sigma

primitive
  prim^glueU : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
             → {A : Type ℓ [ φ ↦ T i0 ]}
             → PartialP φ (T i1) → outS A → primHComp T (outS A)
  prim^unglueU : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
               → {A : Type ℓ [ φ ↦ T i0 ]}
               → primHComp T (outS A) → outS A
  -- Needed for transp.
  primFaceForall : (I → I) → I

transpProof : ∀ {l} (e : I → Type l) (φ : I)
            → (a : Partial φ (e i0))
            → (b : e i1 [ φ ↦ (λ o → transp (λ i → e i) i0 (a o)) ] )
            → Σ λ (x : e i0) → (transp (λ i → e i) i0 x ≡ outS b)
transpProof e φ a b = g i1 , λ j →
  comp e (∂ j ∨ φ) (λ where
    i (φ = i1) → transp (λ j → e (j ∧ i)) (~ i) (a 1=1)
    i (j = i0) → transp (λ j → e (j ∧ i)) (~ i) (g i1)
    i (j = i1) → g (~ i)
    i (i = i0) → g i1)
      where
      sys : (l : I) → Partial (φ ∨ ~ φ ∨ ~ l) (e (~ l))
      sys l (φ = i1) = transp (λ j → e (j ∧ ~ l)) l (a 1=1)
      sys l (φ = i0) = transp (λ j → e (~ j ∨ ~ l)) (~ l) (outS b)
      sys l (l = i0) = outS b

      g : (k : I) → e (~ k)
      g k = fill (λ i → e (~ i)) (∂ φ) k sys

{-# BUILTIN TRANSPPROOF transpProof #-}
