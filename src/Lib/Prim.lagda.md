Lane Biocini
May 04, 2024

```
{-# OPTIONS --safe #-}

module Lib.Prim where

infixl -1 _type
infixl 70 _⁺⁺ _⁺⁺⁺

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
