```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Interval where

open import Prim.Type using ( Level; Type; _₊ )

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

-- Import the core primitives early
--import Agda.Builtin.Cubical.HCompU

iconst : ∀ {u} {@0 A : Type u} → A → I → A
iconst a _ = a
{-# INLINE iconst #-}

ieq : I → I → I
ieq i j = (i ∧ j) ∨ (~ i ∧ ~ j)

ierp : I → I → I → I
ierp i j k = (~ k ∧ i) ∨ (k ∧ j) ∨ (i ∧ j)

```

```
infixl 70 ∂

∂ : I → I
∂ i = ~ i ∨ i

module ∂ where
  open import Agda.Builtin.Cubical.Path
  contract : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → Type (ℓ (i ∨ j))
  contract A i j = A (i ∨ j)

  extend : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → Type (ℓ (i ∧ j))
  extend A i j = A (i ∧ j)

  cover : {@0 ℓ : I → Level} {@0 A : ∀ i → Type (ℓ i)}
        → (φ : I)
        → (P : ∀ k → A (φ ∧ k) → Type (ℓ (φ ∧ k)))
        → (∀ k → A k)
        → (i : I) → Type (ℓ (φ ∧ i))
  cover φ P f i = P (φ ∧ i) (f (φ ∧ i))

  sym : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → Type (ℓ (~ i))
  sym A i = A (~ i)

  line : ∀ {u v} {@0 A : I → Type u}
       → (P : ∀ {i} → A i → Type v)
       → ∀ {@0 x y} → PathP A x y
       → (i : I) → Type v
  line P q i = P (q i)

  square : ∀ {u v} {@0 A : Type u} {@0 x : A}
         → (P : (y : A) → x ≡ y → Type v)
         → {@0 y : A} → x ≡ y → (i : I) → Type v
  square P q i = P (q i) (λ j → q (i ∧ j))

  square#0 : ∀ {u v} {@0 A : Type u} {@0 x : A}
         → (P : ∀ (@0 y) → @0 x ≡ y → Type v)
         → {@0 y : A} → @0 x ≡ y → (i : I) → Type v
  square#0 P q i = P (q i) (λ j → q (i ∧ j))
