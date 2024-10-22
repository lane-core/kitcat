Lane Biocini
Oct 13th, 2024

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Function.Inv where

open import Lib.Prim
open import Lib.Data.Sigma using (Σ)

open import Lib.Trait.Cut
open import Lib.Trait.Setoid

open import Lib.Trait.Typoid.Type
open import Lib.Trait.Typoid.Base using (Typoid)
open import Lib.Trait.Typoid.Function.Type

module _ {u₁ v₁ w₁ u₂ v₂ w₂}
 {𝓐 : Typoid u₁ v₁ w₁}
 {𝓑 : Typoid u₂ v₂ w₂}
 where
 private module 𝓐 = Typoid 𝓐
 private module 𝓑 = Typoid 𝓑

 -- Proposition 2.7 from Petrakis' paper
 -- Is the proof elegant? Probably not, we need to split this proof
 -- into a bunch of smaller lemmas. But at least it is done.
 module _ {f : 𝓐.ob → 𝓑.ob} (𝓕 : is-typoid-function 𝓐 𝓑 f) where
  open is-typoid-function 𝓕 renaming (1-associate to ϕ; 2-associate to ϕ²)
  inv-contravariance : ∀ {x y} (e : x 𝓐.≃ y)
                     → ϕ y x (𝓐.inv e) 𝓑.≅ 𝓑.inv (ϕ x y e)
  inv-contravariance {x} {y} e =
     ϕ y x (e ⁻¹)                                  ⟩ I
   ≡ ϕ y x (𝓐.inv e ∙ 𝓐.eqv x)                     ⟩ II
   ≡ ϕ y x (𝓐.inv e ∙ (e ∙ 𝓐.inv e))               ⟩ III
   ≡ ϕ y x (𝓐.inv e ∙ e ∙ 𝓐.inv e)                 ⟩ IV
   ≡ ϕ y y (𝓐.inv e ∙ e) ∙ ϕ y x (𝓐.inv e)         ⟩ V
   ≡ 𝓑.inv (ϕ x y e) ∙ ϕ x y e ∙ ϕ y x (𝓐.inv e)   ⟩ VI
   ≡ 𝓑.inv (ϕ x y e) ∙ (ϕ x y e ∙ ϕ y x (𝓐.inv e)) ⟩ VII
   ≡ 𝓑.inv (ϕ x y e) ∙ 𝓑.eqv (f x) ⟩ VIII
   ≡ 𝓑.eqv2 (𝓑.inv (ϕ x y e))
    where
    I : ϕ y x (𝓐.inv e) 𝓑.≅ ϕ y x (𝓐.inv e ∙ 𝓐.eqv x)
    I = ϕ² y x (𝓐.inv e) (𝓐.inv e ∙ 𝓐.eqv x) (𝓐.inv2 (𝓐.eqvr (𝓐.inv e)))

    II : ϕ y x (𝓐.inv e ∙ 𝓐.eqv x) 𝓑.≅ ϕ y x (𝓐.inv e ∙ (e ∙ 𝓐.inv e))
    II = ϕ² y x
     (𝓐.inv e ∙ 𝓐.eqv x)
     (𝓐.inv e ∙ (e ∙ 𝓐.inv e))
     (𝓐.hcomp (𝓐.eqv2 (𝓐.inv e)) (𝓐.inv2 (𝓐.invr e)))

    III : ϕ y x (𝓐.concat (𝓐.inv e) (𝓐.concat e (𝓐.inv e)))
      𝓑.≅ ϕ y x (𝓐.concat (𝓐.concat (𝓐.inv e) e) (𝓐.inv e))
    III = ϕ² y x
     (𝓐.concat (𝓐.inv e) (𝓐.concat e (𝓐.inv e)))
     (𝓐.concat (𝓐.concat (𝓐.inv e) e) (𝓐.inv e))
     (𝓐.inv2 (𝓐.assoc (𝓐.inv e) e (𝓐.inv e)))

    IV : ϕ y x (𝓐.inv e ∙ e ∙ 𝓐.inv e)
     𝓑.≅ ϕ y y (𝓐.inv e ∙ e) ∙ ϕ y x (𝓐.inv e)
    IV = associate-comp (𝓐.inv e ∙ e) (𝓐.inv e)

    V : 𝓑.concat (ϕ y y (𝓐.inv e ∙ e)) (ϕ y x (𝓐.inv e))
     𝓑.≅ 𝓑.concat (𝓑.inv (ϕ x y e) ∙ ϕ x y e) (ϕ y x (𝓐.inv e))
    V = 𝓑.hcomp (associate-comp (𝓐.inv e) e ∙ i) (𝓑.eqv2 (ϕ y x (𝓐.inv e)))
     where
     i : ϕ y x (𝓐.inv e) ∙ ϕ x y e 𝓑.≅ (ϕ x y e) ⁻¹ ∙ ϕ x y e
     i = ϕ y x (𝓐.inv e) ∙ ϕ x y e ⟩ 𝓑.inv2 (associate-comp (𝓐.inv e) e)
       ≡ ϕ y y (𝓐.inv e ∙ e) ⟩ ϕ² y y (e ⁻¹ ∙ e) (𝓐.eqv y) (𝓐.invl e)
       ≡ ϕ y y (𝓐.eqv y) ⟩ associate-id y
       ≡ 𝓑.eqv (f y) ⟩ (𝓑.invl (ϕ x y e)) ⁻¹
       ≡ 𝓑.eqv2 ((ϕ x y e) ⁻¹ ∙ ϕ x y e)

    VI : 𝓑.concat (𝓑.concat (𝓑.inv (ϕ x y e)) (ϕ x y e)) (ϕ y x (𝓐.inv e))
     𝓑.≅ 𝓑.concat (𝓑.inv (ϕ x y e)) (𝓑.concat (ϕ x y e) (ϕ y x (𝓐.inv e)))
    VI = 𝓑.assoc (𝓑.inv (ϕ x y e)) (ϕ x y e) (ϕ y x (𝓐.inv e))

    VII : 𝓑.concat (𝓑.inv (ϕ x y e)) (ϕ x y e ∙ ϕ y x (𝓐.inv e))
      𝓑.≅ 𝓑.concat (𝓑.inv (ϕ x y e)) (𝓑.eqv (f x))
    VII = 𝓑.hcomp (𝓑.eqv2 (𝓑.inv (ϕ x y e)))
                  (𝓑.inv2 (associate-comp e (𝓐.inv e))
                   ∙ ϕ² x x (e ∙ 𝓐.inv e) (𝓐.eqv x) (𝓐.invr e)
                   ∙ associate-id x
                   )

    VIII : 𝓑.concat (𝓑.inv (ϕ x y e)) (𝓑.eqv (f x)) 𝓑.≅ 𝓑.inv (ϕ x y e)
    VIII = 𝓑.eqvr (𝓑.inv (ϕ x y e))
