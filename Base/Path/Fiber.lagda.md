Lane Biocini
Aug 3rd, 2024

```agda

{-# OPTIONS --safe #-}

module Base.Path.Fiber where

open import Prim.Prelude
open import Base.Iso
--open import Control.Arrow

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 record fiber (f : A → B) (y : B) : 𝓊 ⊔ 𝓋 type where
  field
   pt : A
   path : f pt ≡ y

 open fiber public

 _$_ : (f : A → B) → (x : A) → (fiber f (f x))
 _$_ f x .pt = x
 _$_ f x .path = refl

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 instance
  Arrow-fiber : {f : A → B} {y : B} → Arrow (fiber f y)
  Arrow-fiber .src = pt
  Arrow-fiber .tgt = λ f → Id.rhs (f .path)

  Underlying-fiber : {f : A → B} {y : B} → Underlying (fiber f y)
  Underlying-fiber .Underlying.ℓ = 𝓋
  Underlying-fiber {f} {y} .⌞_⌟ = λ fib → f (fib .pt) ≡ y

module _ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : 𝓌 type}
               {f : A → B} {g : B → C} {y : B} {z : C} where
 instance
  Cut-fiber : Cut B
              (λ y → fiber g (g y))
              λ {y} p → fiber (g ∘ f) (g (p .pt)) → fiber (g ∘ f) (g y)
  Cut-fiber .seq {f} q p .pt = pt p
  Cut-fiber .seq {f} q p .path = path p ∙ path q
