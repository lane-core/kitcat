Lane Biocini
August 18th, 2024

```agda

{-# OPTIONS --safe #-}

module Base.Iso where

open import Prim.Prelude

sym-is-inverse : ∀ {𝓊} {A : 𝓊 type} {x y : A} (p : x ≡ y)
                → Id.inv p ∙ p ≡ refl
sym-is-inverse refl = refl

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 inverse : (A → B) → (B → A) → 𝓋 type
 inverse g f = g ∘ f ∼ id {𝓋} {B}
{-# DISPLAY inverse g f = g ∘ f ∼ id #-}

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 record has-inverse (f : A → B) : 𝓊 ⊔ 𝓋 type where
  infixl 35 iso

  field
   iso : B → A
   is-retr : inverse f iso
   is-sec : inverse iso f

  syntax iso b = b ⁻¹

 open has-inverse ⦃ ... ⦄ public

 is-section : (s : A → B) → 𝓊 ⊔ 𝓋 type
 is-section s = Σ r ꞉ (B → A) , inverse r s

 is-retraction : (r : A → B) → 𝓊 ⊔ 𝓋 type
 is-retraction r = Σ s ꞉ (B → A) , inverse r s

```

The conventional definition of Isomorphism in 1lab and TypeToplogy

```

record Iso {𝓊 𝓋} (A : 𝓊 type) (B : 𝓋 type) : 𝓊 ⊔ 𝓋 type where
 field
  has-iso : A → B
  is-iso : has-inverse has-iso

open Iso public

_≅_ : ∀ {𝓊 𝓋} (A : 𝓊 type) (B : 𝓋 type) → 𝓊 ⊔ 𝓋 type
_≅_ = Iso

instance
 id-has-inverse : ∀ {𝓊} {A : 𝓊 type} {x y : A}
                → has-inverse (Id.inv {𝓊} {A} {x} {y})
 id-has-inverse .iso = Id.inv
 id-has-inverse .is-retr refl = refl
 id-has-inverse .is-sec refl = refl


module iso where
 rfl : ∀ {𝓊} → {A : 𝓊 type} → A ≅ A
 rfl .has-iso = id
 rfl .is-iso .iso = id
 rfl .is-iso .is-sec = htpy.idn id
 rfl .is-iso .is-retr = htpy.idn id

 inv : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} → A ≅ B → B ≅ A
 inv p .has-iso = p .is-iso has-inverse.⁻¹
 inv p .is-iso .iso = p .has-iso
 inv p .is-iso .is-retr = p .is-iso .is-sec
 inv p .is-iso .is-sec = p .is-iso .is-retr

 concat : ∀ {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} {C : 𝓌 type}
        → A ≅ B → B ≅ C → A ≅ C
 concat g f .has-iso = λ x → α (β x) where
  open Iso f renaming (has-iso to α)
  open Iso g renaming (has-iso to β)
 concat g f .is-iso .iso = λ x → δ (σ x) where
  open has-inverse (g .is-iso) renaming (iso to δ)
  open has-inverse (f .is-iso) renaming (iso to σ)
 concat g f .is-iso .is-retr =
  α ∘ β ∘ δ ∘ σ ⊢ htpy.lwhisker α (htpy.rwhisker i σ) ,
  α ∘ σ ⊢ ii ,
  htpy.idn id where
   open Iso f renaming (has-iso to α)
   open Iso g renaming (has-iso to β)
   open has-inverse (g .is-iso) renaming (iso to δ ; is-retr to i)
   open has-inverse (f .is-iso) renaming (iso to σ ; is-retr to ii)
 concat g f .is-iso .is-sec =
  δ ∘ σ ∘ α ∘ β ⊢ htpy.lwhisker δ (htpy.rwhisker i β) ,
  δ ∘ β ⊢ ii ,
  htpy.idn id where
   open Iso f renaming (has-iso to α)
   open Iso g renaming (has-iso to β)
   open has-inverse (f .is-iso) renaming (iso to σ ; is-sec to i)
   open has-inverse (g .is-iso) renaming (iso to δ ; is-sec to ii)

```

We also have the Joyal (symmetric) notion of equivalence that TypeTopology
uses in this module, because its little work to introduce it here.

```

is-jequiv : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} (f : A → B) → 𝓊 ⊔ 𝓋 type
is-jequiv f = is-retraction f × is-section f

```

Define Global instances

```

module _ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 instance
  Arrow-iso : Arrow (A ≅ B)
  Arrow-iso .src _ = A
  Arrow-iso .tgt _ = B

module _ {𝓊 𝓋 𝓌} {B : 𝓋 type} {C : 𝓌 type} where
 instance
  Cut-iso : Cut (𝓊 type)
                (λ A → A ≅ B)
                λ p → tgt p ≅ C → src p ≅ C
  Cut-iso .seq {A} = iso.concat {𝓊} {𝓋} {𝓌} {A} {B} {C}
