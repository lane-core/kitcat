Lane Biocini

A pragmatic compromise between type theories

```agda

{-# OPTIONS --safe --cubical-compatible #-}

open import Lib.Core.Equal.Type

module Lib.Core.Equal (E : Equality) where

open import Lib.Core.Prim
open import Lib.Core.Type

open Equality E public

cong2 : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
    → (f : A → B → C)
    → {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ＝ a₂
    → b₁ ＝ b₂
    → f a₁ b₁ ＝ f a₂ b₂
cong2 f {a₁} {a₂} {b₁} {b₂} p q = (cong (λ a → f a b₁) p) ∙ (cong (λ b → f a₂ b) q)

erefl : ∀ {u} {A : Type u} (x : A) → x ＝ x
erefl x = refl {x = x}

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = _＝_

Singl : ∀ {u} {A : Type u} → A → Type u
Singl {A = A} x = Σ (λ a → (x ＝ a))
{-# INLINE Singl #-}

subst : ∀ {u v} {A : Type u} (P : A → Type v)
      → ∀ {x y} (q : x ＝ y) → P x → P y
subst P q = transport (cong P q)
{-# INLINE subst #-}

replace : ∀ {u v} {A : Type u} {P : A → Type v}
    → ∀ {x y} (q : x ＝ y) → P x → P y
replace {P} = subst P

rwt : ∀ {u v} {A : Type u} (P : A → Type v)
    → ∀ {x y} (q : x ＝ y) → P y → P x
rwt P p = replace (sym p)
{-# INLINE rwt #-}

J : ∀ {u v} {A : Type u} {x : A}
  → (P : ∀ y → x ＝ y → Type v)
  → P x refl → ∀ {y} (q : x ＝ y)
  → P y q
J  {v = v} {x = x} P c {y} q = subst (λ (x , p) → P x p) (Singl-contr (y , q)) c
{-# INLINE J #-}

J-refl : ∀ {u v} {A : Type u} {x : A}
       → (P : ∀ y → x ＝ y → Type v)
       → (c : P x refl)
       → J P c refl ＝ c
J-refl {x} = transport-path x
{-# INLINE J-refl #-}

×-to-path : ∀ {u} {A : Type u} → {w x y z : A} → w ＝ y → x ＝ z → (w , x) ＝ (y , z)
×-to-path = cong2 _,_

subst2 : ∀ {u v w} {A : Type u} {B : Type v} (P : A → B → Type w)
       → {w y : A} {x z : B} → w ＝ y → x ＝ z → P w x → P y z
subst2 {A} {B} P {w} {y} {x} {z} q s = subst (λ ((x , y) : A × B) → P x y) (cong2 _,_ q s)

Ω : ∀ {u} → Type* u → Type u
Ω (_ , a) = a ＝ a
{-# INLINE Ω #-}

Loop : ∀ {u} → Type* u → Type* u
Loop A .fst = Ω A
Loop A .snd = refl

record is-contr {u} (A : Type u) : Type u where
  constructor contr
  field
    center : A
    paths : (y : A) → center ＝ y

open is-contr public
{-# INLINE contr #-}

is-prop : ∀ {u} → Type u → Type u
is-prop A = (x y : A) → x ＝ y
{-# INLINE is-prop #-}

is-set : ∀ {u} → Type u → Type u
is-set A = (x y : A) → is-prop (x ＝ y)
{-# INLINE is-set #-}

is-groupoid : ∀ {u} → Type u → Type u
is-groupoid A = (x y : A) → is-set (x ＝ y)
{-# INLINE is-groupoid #-}

is-hlevel : ∀ {u} → Nat → Type u → Type u
is-hlevel Z A = is-contr A
is-hlevel (S Z) A = is-prop A
is-hlevel (S (S n)) A = ∀ x y → is-hlevel n (Path A x y)
{-# INLINE is-hlevel #-}

record is-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    unit : (x : A) → inv (f x) ＝ x
    counit : (y : B) → f (inv y) ＝ y

Qinv : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Qinv A B = Σ (λ (f : A → B) → is-qinv f)
infix 6 Qinv

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    unit : (x : A) → inv (f x) ＝ x
    counit : (y : B) → f (inv y) ＝ y
    adj : (x : A) → cong f (unit x) ＝ counit (f x)

_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
_≃_ A B = Σ (λ (f : A → B) → is-equiv f)
infix 6 _≃_

fiber : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → B → Type (u ⊔ v)
fiber f y = Σ (λ x → f x ＝ y)
