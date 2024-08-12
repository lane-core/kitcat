Lane Biocini
Aug 3rd, 2024

```agda

{-# OPTIONS --safe #-}

module Base.Path.Fiber where

open import Prim.Prelude

sym-is-inverse : ∀ {𝓊} {A : 𝓊 type} {x y : A} (p : x ≡ y)
                → refl ≡ ((Id.inv p) ∙ p)
sym-is-inverse refl = refl

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 fiber : (A → B) → B → 𝓊 ⊔ 𝓋 type
 fiber f y = Σ x ꞉ A , f x ≡ y

 instance
  arrow-fiber : {f : A → B} {y : B} → Arrow (fiber f y)
  arrow-fiber .src = fst
  arrow-fiber .tgt = λ f → Id.rhs (f .snd)

  underlying-fiber : {f : A → B} {y : B} → Underlying (fiber f y)
  underlying-fiber .Underlying.ℓ = 𝓋
  underlying-fiber {f} {y} .⌞_⌟ = λ fib → f (fib .fst) ≡ y
