```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Core.Prim where

open import Agda.Primitive public
  using ( SSet
        ; SSetω
        ; LevelUniv
        ; Level )
  renaming ( Set   to Type
           ; Setω  to Typeω
           ; _⊔_ to infixl 6 _⊔_
           ; lsuc to infixr 7 _₊
           ; lzero to 0ℓ )

1ℓ : Level
1ℓ = 0ℓ ₊

record Lift {u} a (A : Type u) : Type (u ⊔ a) where
  constructor liftℓ
  field
    lower : A

open Lift public

level-of : ∀ {ℓ} {A : Type ℓ} → A → Level
level-of {ℓ} _ = ℓ

Type₊ : ∀ ℓ → Type (ℓ ₊ ₊)
Type₊ ℓ = Type (ℓ ₊)

𝓤 : Typeω
𝓤 = (u : Level) → Type u

record Underlying {ℓ} (A : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟   : A → Type ℓ-underlying

open Underlying ⦃ ... ⦄ public
{-# DISPLAY Underlying.⌞_⌟ _ X = ⌞ X ⌟ #-}

instance
  Underlying-Type : ∀ {ℓ} → Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟  = λ x → x

  Underlying-Lift : ∀ {ℓ ℓ'} {A : Type ℓ}
                  → ⦃ ua : Underlying A ⦄
                  → Underlying (Lift ℓ' A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟ x = ⌞ x .lower ⌟

Π : ∀ {u v} {A : Type u} → (A → Type v) → Type (u ⊔ v)
Π B = ∀ x → B x

id : ∀ {u} {@0 A : Type u} → A → A
id = λ x → x
{-# INLINE id #-}

idfun : ∀ {u} (@0 A : Type u) → A → A
idfun A = λ x → x
{-# INLINE idfun #-}

const : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A → B → A
const a ._ = a
{-# INLINE const #-}

_∘_ : ∀ {u v w} {@0 A : Type u} {@0 B : A → Type v} {@0 C : ∀ a → B a → Type w}
     → ({x : A} (y : B x) → C x y) → (f : Π B) (x : A) → C x (f x)
_∘_ g f = λ x → g {x} (f x)
infixr 9 _∘_
{-# INLINE _∘_ #-}

module Unit where
  open import Agda.Builtin.Unit public

  ind : ∀ {u} (P : @0 ⊤ → Type u) (p : P tt) → (@0 x : ⊤) → P x
  ind P p ._ = p

  Unit : ∀ {u} → Type u
  Unit {u} = Lift u ⊤

open Unit using (Unit; ⊤; tt) public

instance
  Lift-Unit : ∀ {u} → Unit {u}
  Lift-Unit .lower = tt
