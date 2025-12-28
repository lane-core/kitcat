A great many proofs are more or less transcripted from 1lab here, and perhaps I will adopt their
hlevel machinery but depending on how the core library turns out I may have other mechanisms to
consider

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Core.HLevel where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Sub
open import Lib.Core.Kan
open import Lib.Core.Type
open import Lib.Core.Path
open import Lib.Core.Equiv
open import Lib.Core.Transport

is-hlevel : ∀ {u} → Nat → Type u → Type u
is-hlevel Z A = is-contr A
is-hlevel (S Z) A = is-prop A
is-hlevel (S (S n)) A = (x y : A) → is-hlevel (S n) A

record Tr : Type where
  constructor hlevel
  field
    level : Nat

record N-type u n : Type₊ u where
  no-eta-equality
  field
    ∣_∣ : Type u
    trunc : is-hlevel n ∣_∣

Π-is-prop : ∀ {u v} {A : Type u} {B : A → Type v}
          → ((a : A) → is-prop (B a))
          → is-prop ((a : A) → B a)
Π-is-prop prop f g i = λ a → prop a (f a) (g a) i


Πi-is-prop : ∀ {u v} {A : Type u} {B : A → Type v}
           → ((a : A) → is-prop (B a))
           → is-prop ({a : A} → B a)
Πi-is-prop prop f g i {a} = prop a f g i

×-path : ∀ {u u'} {A : Type u} {B : Type u'} {x y : A × B}
       → x .fst ≡ y .fst → x .snd ≡ y .snd → x ≡ y
×-path p q i = p i , q i

is-contr-equiv : ∀ {u v} {A : Type u} {B : Type v}
               → A ≃ B → is-contr B → is-contr A
is-contr-equiv e bcontr = record { center = ctr ; paths = pths }
  where
    open Equiv e
    ctr : _
    ctr = inv (bcontr .center)

    pths : _
    pths x = ap inv (bcontr .paths (fwd x)) ∙ unit x

-- Product of contractible types is contractible
is-contr-× : ∀ {u u'} {A : Type u} {B : Type u'}
           → is-contr A → is-contr B → is-contr (A × B)
is-contr-× cA cB .center = cA .center , cB .center
is-contr-× cA cB .paths (a , b) = ×-path (cA .paths a) (cB .paths b)

is-prop-× : ∀ {u v} {A : Type u} {B : Type v}
          → is-prop A → is-prop B → is-prop (A × B)
is-prop-× aprop bprop (a , b) (a' , b') i = aprop a a' i , bprop b b' i

is-prop-equiv : ∀ {u v} {A : Type u} {B : Type v}
              → A ≃ B → is-prop B → is-prop A
is-prop-equiv e bprop x y = equiv-path
  where
    open Equiv e
    equiv-path : x ≡ y
    equiv-path = sym (unit x) ∙ ap inv (bprop (fwd x) (fwd y)) ∙ unit y

Σ-path
  : ∀ {u v} {A : Type u} {B : A → Type v} (bp : ∀ x → is-prop (B x))
  → {x y : Σ B}
  → (x .fst ≡ y .fst) → x ≡ y
Σ-path bp {x} {y} p i =
  p i , is-prop→PathP (λ i → bp (p i)) (x .snd) (y .snd) i

Σ-is-prop : ∀ {u u'} {A : Type u} {B : A → Type u'}
          → is-prop A → (∀ a → is-prop (B a)) → is-prop (Σ B)
Σ-is-prop aprop bprop (a₁ , b₁) (a₂ , b₂) = Σ-path bprop (aprop a₁ a₂)

-- If A is contractible, then Σ y : A, x ≡ y is contractible for any x : A
singl-contr-in-contr : ∀ {u} {A : Type u} → is-contr A → (x : A) → is-contr (Σ y ∶ A , x ≡ y)
singl-contr-in-contr c x .center = x , refl
singl-contr-in-contr c x .paths (y , p) = Σ-path (is-contr→is-set c x) p

subst-prop : ∀ {u u'} {A : Type u} {P : A → Type u'} → is-prop A → ∀ a → P a → ∀ b → P b
subst-prop {P = P} prop a pa b = subst P (prop a b) pa

-- maps between contractible types have contractible fibers
contr→contr-fiber : ∀ {u u'} {A : Type u} {B : Type u'}
                  → (f : A → B) → is-contr A → is-contr B
                  → ∀ b → is-contr (Σ a ∶ A , f a ≡ b)
contr→contr-fiber {A} f acontr bcontr b = prop-inhabited→is-contr fiber-is-prop fiber-inhabited
  where
    β : (x : A) → is-prop (f x ≡ b)
    β x f g = is-contr→is-set bcontr _ _ f g

    fiber-is-prop : is-prop (Σ a ∶ A , f a ≡ b)
    fiber-is-prop (a₁ , p₁) (a₂ , p₂) = Σ-path β (is-contr→is-prop acontr a₁ a₂)

    fiber-inhabited : Σ a ∶ A , f a ≡ b
    fiber-inhabited = acontr .center , is-contr→is-prop bcontr _ _

module _ {u v} {A : Type u} {B : Type v} where
  injective : (A → B) → Type _
  injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  injective→is-embedding
    : is-set B → (f : A → B) → injective f
    → ∀ x → is-prop (fiber f x)
  injective→is-embedding bset f inj x (f*x , p) (f*x' , q) =
    Σ-path (λ x → bset _ _) (inj (p ∙ sym q))

  has-prop-fibres→injective
    : (f : A → B) → (∀ x → is-prop (fiber f x))
    → injective f
  has-prop-fibres→injective f prop {x} {y} p =
    ap fst (prop (f y) (x , p) (y , refl))

  is-embedding : (A → B) → Type _
  is-embedding f = ∀ x → is-prop (fiber f x)

_↪_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ↪ B = Σ f ∶ (A → B) , is-embedding f
