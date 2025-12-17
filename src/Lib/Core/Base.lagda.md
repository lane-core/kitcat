```agda
{-# OPTIONS --safe --erased-cubical --no-sized-types #-}

module Lib.Core.Base where

open import Lib.Core.Prim using (Level; Type; _⊔_; _₊; Typeω; SSetω; 0ℓ)

open import Agda.Primitive.Cubical public
  using ( IUniv   -- IUniv : SSet₁
        ; I       -- I : IUniv
        ; i0      -- i0 : I
        ; i1      -- i1 : I
        ; IsOne   -- IsOne : I → Typeω
        ; Partial -- Partial : ∀{ℓ} (i : I) (A : Type ℓ) → Type ℓ
                  -- Partial i A = IsOne i → A
        ; PartialP
        ; primPOr
        )
  renaming ( primIMin to _∧_ -- _∧_ : I → I → I
           ; primIMax to _∨_ -- _∨_ : I → I → I
           ; primINeg to ~_  -- ~_ : I → I
           ; itIsOne    to 1=1       -- 1=1 : IsOne i1
           ; isOneEmpty to is1-empty -- is1-empty : ∀ {ℓ} {A : Partial i0 (Type ℓ)}
                                     --           → PartialP i0 A
           ; IsOne1     to is1-left  -- is1-left  : ∀ i j → IsOne i → IsOne (i ∨ j)
           ; IsOne2     to is1-right -- is1-right : ∀ i j → IsOne j → IsOne (i ∨ j)
           )

-- Import the core primitives early?
-- import Agda.Builtin.Cubical.HCompU

ILevel : Type
ILevel = I → Level

IType : ∀ u → Type (u ₊)
IType u = I → Type u

DType : (u : ILevel) → SSetω
DType u = ∀ i → Type (u i)

iconst : ∀ {u} {@0 A : Type u} → A → I → A
iconst a _ = a
{-# INLINE iconst #-}

iflip : ∀ {u} {@0 A : I → I → Type u} → (∀ i j → A i j) → ∀ i j → A j i
iflip {A} f = λ j i → f i j
{-# INLINE iflip #-}

ieq : I → I → I
ieq i j = (i ∧ j) ∨ (~ i ∧ ~ j)

ierp : I → I → I → I
ierp t x y = (x ∧ ~ t) ∨ (y ∧ (t ∨ x))
{-# INLINE ierp #-}

imp : I → I → I
imp x y = ~ x ∨ y
{-# INLINE imp #-}

```

Short path module (maybe goes in Lib.Data.Path?)

```

open import Agda.Builtin.Cubical.Path public
  renaming (_≡_ to infix 2 _≡_)

_[_≡_] pathp-syntax : ∀ {u} (A : I → Type u) → A i0 → A i1 → Type u
_[_≡_] = PathP
pathp-syntax = PathP
{-# DISPLAY pathp-syntax = PathP #-}
syntax pathp-syntax A x y = x ≡ y ∶ A

infixl 70 ∂

∂ : I → I
∂ i = ~ i ∨ i

module ∂ where
  contract : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → Type (ℓ (i ∨ j))
  contract A i j = A (i ∨ j)
  {-# INLINE contract #-}

  extend : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → Type (ℓ (i ∧ j))
  extend A i j = A (i ∧ j)
  {-# INLINE extend #-}

  cover : {@0 ℓ : I → Level} {@0 A : ∀ i → Type (ℓ i)}
        → (φ : I)
        → (P : ∀ k → A (φ ∧ k) → Type (ℓ (φ ∧ k)))
        → (∀ k → A k)
        → (i : I) → Type (ℓ (φ ∧ i))
  cover φ P f i = P (φ ∧ i) (f (φ ∧ i))
  {-# INLINE cover #-}

  sym : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → Type (ℓ (~ i))
  sym A i = A (~ i)
  {-# INLINE sym #-}

  line : ∀ {u v} {@0 A : I → Type u}
       → (P : ∀ {i} → A i → Type v)
       → ∀ {@0 x y} → PathP A x y
       → (i : I) → Type v
  line P q i = P (q i)
  {-# INLINE line #-}

  square : ∀ {u v} {A : I → Type u}
         → (P : {i : I} → A i → A i → Type v)
         → {x x' : A i0} {y y' : A i1}
         → x ≡ y ∶ A → x' ≡ y' ∶ A
         → (i : I) → Type v
  square R f g i = R (f i) (g i)
  {-# INLINE square #-}

  cube : ∀ {u v} {A : I → I → Type u}
       → (P : {i j : I} → A i j → A i j → Type v)
       → {x x' : ∀ i → A i i0} {y y' : ∀ i → A i i1}
       → (p : PathP (A i0) (x i0) (y i0))
       → (p' : PathP (A i0) (x' i0) (y' i0))
       → (q : PathP (A i1) (x i1) (y i1))
       → (q' : PathP (A i1) (x' i1) (y' i1))
       → p ≡ q ∶ (λ i → x i ≡ y i ∶ λ j → A i j)
       → p' ≡ q' ∶ (λ i → x' i ≡ y' i ∶ λ j → A i j)
       → (i j : I) → Type v
  cube P p p' q q' f g i j = P (f i j) (g i j)
  {-# INLINE cube #-}

_~ᵢ_ : ∀ {u} {A : I → Type u} → (∀ i → A i) → (∀ i → A i) → Type u
f ~ᵢ g = ∀ i → f i ≡ g i

infixr 40 _∘ᵢ_
_∘ᵢ_ : ∀ {u} {v : I → Level} {A : I → Type u} {B : ∀ i → A i → Type (v i)}
     → (g : ∀ i (a : A i) → B i a)
     → (f : ∀ i → A i)
     → ∀ i → B i (f i)
_∘ᵢ_ g f = λ i → g i (f i)

