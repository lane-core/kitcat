Lane Biocini
Oct 13th, 2024

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Function.Comp where

open import Lib.Prim
open import Lib.Data.Sigma using (fst; snd)
open import Lib.Trait.Typoid.Base using (Typoid)
open import Lib.Trait.Typoid.Function.Type
open import Lib.Trait.Cut

module _ {u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃}
 {𝓐 : Typoid u₁ v₁ w₁}
 {𝓑 : Typoid u₂ v₂ w₂}
 {𝓒 : Typoid u₃ v₃ w₃}
 where
 private module 𝓐 = Typoid 𝓐
 private module 𝓑 = Typoid 𝓑
 private module 𝓒 = Typoid 𝓒

 module _ {f : 𝓐.ob → 𝓑.ob} {g : 𝓑.ob → 𝓒.ob}
  (𝓕 : is-typoid-function 𝓐 𝓑 f)
  (𝓖 : is-typoid-function 𝓑 𝓒 g)
  where
  private
   module 𝓕 = is-typoid-function 𝓕 renaming (1-associate to ϕ; 2-associate to ϕ²)
   module 𝓖 = is-typoid-function 𝓖 renaming (1-associate to ϕ; 2-associate to ϕ²)

  open is-typoid-function

  typoid-function-comp : is-typoid-function 𝓐 𝓒 (λ x → g (f x))
  typoid-function-comp .has-associate .fst x y e = 𝓖.ϕ (f x) (f y) (𝓕.ϕ x y e)
  typoid-function-comp .has-associate .snd x y e d i =
   𝓖.ϕ² (f x) (f y) (𝓕.ϕ x y e) (𝓕.ϕ x y d) (𝓕.ϕ² x y e d i)
  typoid-function-comp .associate-id x = 𝓖.ϕ² (f x) (f x)
                                          (𝓕.ϕ x x (𝓐.eqv x))
                                          (𝓑.eqv (f x))
                                          (𝓕.associate-id x)
                                       ∙ 𝓖.associate-id (f x)
  typoid-function-comp .associate-comp {x} {y} {z} e₁ e₂ = 𝓖.ϕ² (f x) (f z)
                                                            (𝓕.ϕ x z (e₁ ∙ e₂))
                                                            (𝓕.ϕ x y e₁ ∙ 𝓕.ϕ y z e₂)
                                                            (𝓕.associate-comp e₁ e₂)
                                                         ∙ 𝓖.associate-comp (𝓕.ϕ x y e₁)
                                                                            (𝓕.ϕ y z e₂)

  -- TODO "If f, g are strict with respect to 𝓕.ϕ, then g ∘ f is strict wrt to (𝓖 ∘ 𝓕).ϕ"
