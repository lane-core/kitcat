Lane Biocini
August 5th 2024

```agda

{-# OPTIONS --safe #-}

module Base.Path.Contr where

open import Base.Core
open import Base.Path.Prop

module contr where
 record is-contr {𝓊} (A : 𝓊 type) : 𝓊 type where
  constructor mk
  field
   ctr : A
   paths : (x : A) → ctr ≡ x

 open is-contr public

 unit : ∀ {𝓊} → is-contr (𝟙 {𝓊})
 unit .ctr = ⋆
 unit .paths = λ _ → refl

 hsuc : ∀ {𝓊} {A : 𝓊 type} → is-contr A → is-prop A
 hsuc (mk c p) a = tr (λ - → ∀ b → - ≡ b) (p a) p

 -- to-equiv : ∀ {𝓊 𝓋} {A : 𝓊 type} {B : 𝓋 type}
 --          → is-contr A → is-contr B
 --          → {f : A → B}
 --          → is-equiv f
 -- to-equiv Ac Bc = (const (Ac .ctr)
 --                    , λ x → Id.concat (hsuc Bc _ _) (Bc .paths x))
 --                , const (Ac .ctr)
 --                    , λ x → Id.concat (hsuc Ac _ _) (Ac .paths x)


open contr using (is-contr) public
