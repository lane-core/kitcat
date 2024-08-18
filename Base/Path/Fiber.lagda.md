Lane Biocini
Aug 3rd, 2024

```agda

{-# OPTIONS --safe #-}

module Base.Path.Fiber where

open import Prim.Prelude
open import Base.Iso

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 record Fiber (f : A → B) (y : B) : 𝓊 ⊔ 𝓋 type where
  constructor fib
  field
   pt : A
   path : f pt ≡ y

 open Fiber public

 _$_ : (f : A → B) → (x : A) → (Fiber f (f x))
 _$_ f x .pt = x
 _$_ f x .path = refl

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 instance
  Arrow-Fiber : {f : A → B} {y : B} → Arrow (Fiber f y)
  Arrow-Fiber .src = pt
  Arrow-Fiber .tgt = λ f → Id.rhs (f .path)

  Underlying-Fiber : {f : A → B} {y : B} → Underlying (Fiber f y)
  Underlying-Fiber .Underlying.ℓ = 𝓋
  Underlying-Fiber {f} {y} .⌞_⌟ = λ fib → f (fib .pt) ≡ y

module _ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : 𝓌 type}
               {f : A → B} {g : B → C} {y : B} {z : C} where
 instance
  Cut-Fiber : Cut B
              (λ y → Fiber g (g y))
              λ {y} p → Fiber (g ∘ f) (g (p .pt)) → Fiber (g ∘ f) (g y)
  Cut-Fiber .seq {f} q p .pt = pt p
  Cut-Fiber .seq {f} q p .path = path p ∙ path q
