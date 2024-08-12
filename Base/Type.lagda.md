Lane Biocini
May 04, 2024

```agda
{-# OPTIONS --safe #-}

module Base.Type where

open import Base.Core
open import Base.Path.Prop
open import Base.Path.Contr

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

-- path : ∀ {𝓊} (n : Nat) {A : 𝓊 type} → is-hlevel n A → {x y : A} → is-hlevel n (x ≡ y)
-- path zero C {x} {y} .center = contr.hsuc C x y
-- path zero C .paths = prop.hsuc (contr.hsuc C) _ _ _
-- path (suc n) hl = hsuc hl _ _

--  pair : ∀ {𝓊 𝓋} (n : Nat) {A : 𝓊 type} {B : 𝓋 type}
--       → is-hlevel n A
--       → is-hlevel n B
--       → is-hlevel n (A × B)
--  pair n Ahl Bhl = {!!}

--  equiv : ∀ {𝓊 𝓋} (n : Nat) {A : 𝓊 type} {B : 𝓋 type}
--        → is-hlevel n A → is-hlevel n B → is-hlevel n (A ≃ B)
--  equiv zero {A} {B} Ahl Bhl = contr (const (Bhl .center) , c-equiv) γ where
--   c-equiv : is-equiv (const (Bhl .center))
--   c-equiv = contr.to-equiv Ahl Bhl

--   γ : (eqv : A ≃ B) → ((λ _ → Bhl .center) , c-equiv) ≡ eqv
--   γ (f , s) = from ({!!} , {!!})

--  equiv (suc n) Ahl Bhl = {!from ?!}

-- sing : ∀ 𝓊 → 𝓊 ⁺ type
-- sing 𝓊 = 𝓊 hlevel 0

-- Ω : ∀ 𝓊 → 𝓊 ⁺ type
-- Ω 𝓊 = 𝓊 hlevel 1

-- _set : ∀ 𝓊 → 𝓊 ⁺ type
-- 𝓊 set = 𝓊 hlevel 2

-- _grpd : ∀ 𝓊 → 𝓊 ⁺ type
-- 𝓊 grpd = 𝓊 hlevel 3

-- Hom-set : ∀ {𝓊} → 𝓊 type → 𝓊 ⁺ type
-- Hom-set {𝓊} ob = (ob → ob → 𝓊 hlevel 2)

--  -- equiv : ∀ {𝓊} {n : Nat} {A B : 𝓊 type}
--  --               → is-hlevel n A
--  --               → is-hlevel n B
--  --               → is-hlevel n (A ≃ B)
--  -- equiv {𝓊} {zero} {A} hl-a hl-b .center = (λ z → hl-b .is-contr.center)
--  --                                     , ((λ z → hl-a .is-contr.center)
--  --                                       , hl-b .is-contr.paths)
--  --                                     , (λ v → hl-a .is-contr.center)
--  --                                     , hl-a .is-contr.paths
--  -- equiv {𝓊} {zero} {A} hl-a hl-b .paths (a , b) = {!!}
--  -- equiv {𝓊} {suc n} hl-a hl-b = {!!}



-- -- Nat.ind (λ x → is-hlevel (suc x) A → is-hlevel (suc (suc x)) A)
-- --                        (λ P x y → prop.hedberg x
-- --                                    (λ a → (λ v → P x a) , (λ _ _ → refl))
-- --                                    y)
-- --                        step
-- --                        n
-- --   where
-- --    step : (k : Nat) →
-- --            (is-hlevel (suc k) A → is-hlevel (suc (suc k)) A) →
-- --            is-hlevel (suc (suc k)) A → is-hlevel (suc (suc (suc k))) A
-- --    step k hl-s→ss hl-ss x y p q = {!!}
