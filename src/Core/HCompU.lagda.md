Homogeneous composition in the universe.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.HCompU where

open import Core.Base
open import Core.Path
open import Core.Type
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub

private module X where
  open import Agda.Primitive.Cubical public using (primTransp; primHComp)

primitive
  prim^glueU : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
             → {A : Type ℓ [ φ ↦ T i0 ]}
             → PartialP φ (T i1) → outS A → X.primHComp T (outS A)
  prim^unglueU : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
               → {A : Type ℓ [ φ ↦ T i0 ]}
               → X.primHComp T (outS A) → outS A
  -- Needed for transp.
  primFaceForall : (I → I) → I

transp-proof : ∀ {l} (E : I → Type l) (φ : I)
            → (a : Partial φ (E i0))
            → (b : E i1 [ φ ↦ (λ o → transp (λ i → E i) i0 (a o)) ] )
            → Σ λ (x : E i0) → (transp E i0 x ≡ outS b)
transp-proof E φ a b = g i1 , λ j →
  com E (∂ j ∨ φ) λ where
    i (φ = i1) → transp (λ j → E (j ∧ i)) (~ i) (a 1=1)
    i (j = i0) → transp (λ j → E (j ∧ i)) (~ i) (g i1)
    i (j = i1) → g (~ i)
    i (i = i0) → g i1
      where
      sys : (l : I) → Partial (φ ∨ ~ φ ∨ ~ l) (E (~ l))
      sys l (φ = i1) = transp (λ j → E (j ∧ ~ l)) l (a 1=1)
      sys l (φ = i0) = transp (λ j → E (~ j ∨ ~ l)) (~ l) (outS b)
      sys l (l = i0) = outS b

      g : (k : I) → E (~ k)
      g k = fil (λ i → E (~ i)) (∂ φ) k sys
{-# BUILTIN TRANSPPROOF transp-proof #-}
