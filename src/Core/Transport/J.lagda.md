The J eliminator and substitution operations.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Transport.J where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Base

private
  variable
    u v : Level
    A : Type u

```

## Substitution

```agda

subst : ∀ {u v} {A : Type u} (P : A → Type v)
      → ∀ {x y} (q : x ≡ y) → P x → P y
subst P q = transport (ap P q)
{-# INLINE subst #-}

replace : ∀ {u v} {A : Type u} {P : A → Type v}
    → ∀ {x y} (q : x ≡ y) → P x → P y
replace {P} = subst P

rwt : ∀ {u v} {A : Type u} (P : A → Type v)
    → ∀ {x y} (q : x ≡ y) → P y → P x
rwt P p = replace (sym p)
{-# INLINE rwt #-}

```

## J Eliminator

```agda

J0 : ∀ {u v} {@0 A : Type u} {@0 x : A}
  → (P : ∀ (@0 y) → @0 x ≡ y → Type v)
  → P x (λ _ → x) → ∀ {@0 y} (@0 q : x ≡ y) → P y q
J0 {v} P c q = coe01 sq c
  module J0 where
    sq : I → Type v
    sq i = P (q i) (λ j → q (i ∧ j))
{-# DISPLAY coe01 (J0.sq P q _) c = J0 P c q #-}

-- the general J which varies over the interval
J-sys : ∀ {u v} {A : Type u} (φ : I) (s : Sys φ A)
      → (P : (x : A) → sys-composite φ s ≡ x → Type v)
      → P (sys-composite φ s) (sys-filler.plid φ s)
      → {x : A} (α : sys-composite φ s ≡ x)
      → P x α
J-sys φ s P c {x} α = transport (λ i → P (ap fst total i) (ap snd total i)) c
  where
  total : (sys-composite φ s , sys-filler.plid φ s) ≡ (x , α)
  total = SysComp-is-contr φ s .paths (x , α)

-- we recover general J
J : ∀ {u v} {A : Type u} {x : A}
  → (P : ∀ y → x ≡ y → Type v)
  → P x refl
  → ∀ {y} (q : x ≡ y) → P y q
J {x = x} = J-sys i1 (λ _ _ → x)

private
  J-singl : ∀ {u v} {A : Type u} {x : A}
    → (P : ∀ y → x ≡ y → Type v)
    → P x refl → ∀ {y} (q : x ≡ y)
    → P y q
  J-singl  {v = v} {A = A} {x = x} P c {y} q = transport Q c
    where
      s : x , refl ≡ y , q
      s = Singl-contr x .paths (y , q)

      Q : P x refl ≡ P y q
      Q = λ i → P (s i .fst) (s i .snd)
  {-# INLINE J-singl #-}

  J-singl≡J : ∀ {u v} {A : Type u} {x : A} → J-singl {u} {v} {A} {x} ≡ J
  J-singl≡J = refl

J-refl : ∀ {u v} {A : Type u} {x : A}
       → (P : ∀ y → x ≡ y → Type v)
       → (c : P x refl)
       → J P c refl ≡ c
J-refl {x} P = transport-refl
{-# INLINE J-refl #-}

```
