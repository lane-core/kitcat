Lane Biocini
May 04, 2024

```agda
{-# OPTIONS --safe #-}

module Base.Type where

open import Prim.Prelude
open import Base.Path.Prop


is-hlevel : ∀ {𝓊} → Nat → 𝓊 type → 𝓊 type
is-hlevel zero A = is-contr A
is-hlevel (suc zero) A = is-prop A
is-hlevel (suc (suc n)) A = (x y : A) → is-hlevel (suc n) (x ≡ y)
{-# INLINE is-hlevel #-}
{-# DISPLAY is-hlevel 1 A = is-prop A #-}

is-set : ∀ {𝓊} → 𝓊 type → 𝓊 type
is-set A = is-hlevel 2 A
{-# DISPLAY is-hlevel 2 A = is-set A #-}

is-groupoid : ∀ {𝓊} → 𝓊 type → 𝓊 type
is-groupoid A = is-hlevel 3 A
{-# DISPLAY is-hlevel 3 A = is-groupoid A #-}

hlsuc : ∀ {𝓊} {n : Nat} {A : 𝓊 type} → is-hlevel n A → is-hlevel (suc n) A
hlsuc {𝓊} {0} = contr.hsuc
hlsuc {𝓊} {1} = prop-to-set
 module hsuc where
  prop-to-set : ∀ {𝓊} {A : 𝓊 type} → is-prop A → is-set A
  prop-to-set {𝓊} {A} P x y = prop.hedberg x (λ a → (λ v → P x a) , (λ _ _ → refl)) y
hlsuc {𝓊} {suc (suc n)} hl x y = hlsuc (hl x y)

-- We'll follow 1lab 'el' here
module el where
 record nType 𝓊 (n : Nat) : 𝓊 ⁺ type where
  constructor mk
  field
   ∣_∣ : 𝓊 type
   is-tr : is-hlevel n ∣_∣

  nsuc : nType 𝓊 (suc n)
  nsuc .∣_∣ = ∣_∣
  nsuc .is-tr = hlsuc is-tr

 open nType public

 instance
  underlying-nType : ∀ {𝓊 n} → Underlying (nType 𝓊 n)
  underlying-nType {𝓊} .Underlying.ℓ = 𝓊
  underlying-nType .⌞_⌟ A = ∣ A ∣

open el hiding (mk) public

_hlevel_ = nType
