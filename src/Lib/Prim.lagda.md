Lane Biocini
May 04, 2024

```
{-# OPTIONS --safe #-}

module Lib.Prim where

infixl -1 _type
infixl 70 _⁺⁺ _⁺⁺⁺

infix 3 Π Σ
infix -1 Pi Sigma
infixr 4 _,_
infixr 5 _×_

open import Agda.Primitive public
 renaming ( Set to Type
          ; SSet to SSet
          ; Setω to uω
          ; lzero to u₀
          ; lsuc to infixl 6 _⁺
          ; _⊔_ to infixr 5 _⊔_
          ) hiding (Prop) -- we work with the Univalent formulation of Prop

_type : ∀ u → Type (u ⁺)
_type u = Type u
{-# INLINE _type #-}
{-# DISPLAY Type u = u type #-}

_⁺⁺ : Level → Level
u ⁺⁺ = u ⁺ ⁺

_⁺⁺⁺ : Level → Level
u ⁺⁺⁺ = u ⁺ ⁺ ⁺

type-of : ∀ {u} {X : u type} (x : X) → u type
type-of {u} {X} = λ _ → X

level-of : ∀ {u} (X : u type) → Level
level-of {u} X = u

Π : ∀ {u v} {A : u type} (B : A → v type) → u ⊔ v type
Π {u} {v} {A} B = (x : A) → B x
{-# INLINE Π #-}

Pi : ∀ {u v} (A : u type) (B : A → v type) → u ⊔ v type
Pi A B = Π B

syntax Pi A (λ x → b) = Π x ꞉ A , b

id : ∀ {u} {A : u type} → A → A
id = λ - → -
{-# INLINE id #-}

_∘_ : ∀ {u v w} {A : u type} {B : A → v type} {C : (x : A) → B x → w type}
    → ({x : A} → Π (C x)) → (f : Π B) → Π (λ x → C x (f x))
_∘_ g f x = g (f x)
{-# INLINE _∘_ #-}

record Σ {u v} {A : u type} (B : A → v type) : u ⊔ v type where
 constructor _,_
 field
  fst : A
  snd : B fst

open Σ public

Sigma : ∀ {u v} (A : u type) → (A → v type) → u ⊔ v type
Sigma {u} {v} A B = Σ {u} {v} {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

{-# DISPLAY Sigma A B = Σ B #-}
{-# BUILTIN SIGMA Sigma #-}

_×_ Pair : ∀ {𝓊 𝓋} → 𝓊 type → 𝓋 type → 𝓊 ⊔ 𝓋 type
_×_ A B = Sigma A (λ _ → B)
Pair = _×_

record Lift {u} v (A : u type) : u ⊔ v type
 where
 field
  lower : A
