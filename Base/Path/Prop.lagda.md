
```agda

{-# OPTIONS --safe #-}

module Base.Path.Prop where

open import Prim.Prelude
open import Base.Iso

is-wconstant : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type} → (A → B) → 𝓊 ⊔ 𝓋 type
is-wconstant f = ∀ x y → f x ≡ f y

is-collapsible : ∀ {𝓊} → 𝓊 type → 𝓊 type
is-collapsible X = Σ f ꞉ (X → X) , is-wconstant f

has-wconstant-endomaps : ∀ {𝓊} → 𝓊 type → 𝓊 type
has-wconstant-endomaps A = (u v : A) → is-collapsible (u ≡ v)

is-prop : ∀ {𝓊} → 𝓊 type → 𝓊 type
is-prop X = (x y : X) → x ≡ y

is-prop-family : ∀ {𝓊 𝓋} {A : 𝓊 type} (B : A → 𝓋 type) → 𝓊 ⊔ 𝓋 type
is-prop-family B = ∀ x → is-prop (B x)

record Prop {𝓊} (A : 𝓊 type) : 𝓊 type where
 no-eta-equality
 constructor prop
 field
  is-Ω : is-prop A

open Prop ⦃ ... ⦄ public

module prop where
 instance
  empty : ∀ {𝓊} → Prop (𝟘 {𝓊})
  empty .is-Ω p = ex-falso p

  unit : ∀ {𝓊} → Prop (𝟙 {𝓊})
  unit .is-Ω p = const refl

 hedberg : ∀ {𝓊} {A : 𝓊 type} (x : A)
         → ((y : A) → is-collapsible (x ≡ y))
         → (y : A) → is-prop (x ≡ y)
 hedberg {𝓊} {A} x pc y p q = c y p
                            ∙ ap (λ - → Id.inv (f x refl) ∙ -) (κ y p q)
                            ∙ Id.inv (c y q)
  where
   f : (y : A) → x ≡ y → x ≡ y
   f y = pc y .fst

   κ : (y : A) (p q : x ≡ y) → f y p ≡ f y q
   κ y = pc y .snd

   c : (y : A) (r : x ≡ y) → r ≡ (Id.inv (f x refl) ∙ f y r)
   c x refl = sym-is-inverse (pc x .fst refl) ⁻¹

record is-contr {𝓊} (A : 𝓊 type) : 𝓊 type where
  constructor contr
  field
   ctr : A
   paths : (x : A) → ctr ≡ x

open is-contr ⦃ ... ⦄ public

module contr where
 unit : ∀ {𝓊} → is-contr (𝟙 {𝓊})
 unit .ctr = ⋆
 unit .paths = λ _ → refl

 hsuc : ∀ {𝓊} {A : 𝓊 type} → is-contr A → is-prop A
 hsuc (contr c p) a = tr (λ - → ∀ b → - ≡ b) (p a) p
