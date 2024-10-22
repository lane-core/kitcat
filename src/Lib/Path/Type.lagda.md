Lane Biocini
Oct 12th, 2024

Type definitions for our Path type

```

{-# OPTIONS --safe  #-}

module Lib.Path.Type where

infix 0 _≡_

open import Lib.Prim
open import Lib.Data.Bundle using (CoYoneda; apc; path) public

```

Our equality type is Coyoneda applied to the id function for some a.

```

_≡_ : ∀ {u} {A : u type} → A → A → u type
_≡_ {u} = CoYoneda (λ x → x)

Path : ∀ {u} {A : u type} → A → A → u type
Path = CoYoneda (λ x → x)
{-# DISPLAY Path x y = x ≡ y #-}

Id : ∀ {u} (A : u type) → A → A → u type
Id A = Path
{-# DISPLAY Id _ x y = x ≡ y #-}

refl : ∀ {u} {A : u type} {a : A} → a ≡ a
refl {u} {A} {a} = path a
{-# INLINE refl #-}

J : ∀ {u v} {A : u type} {a : A}
  → (P : (x : A) → a ≡ x → v type)
  → {x : A} (q : a ≡ x) → P a refl → P x q
J P {x} (path .x) p = p
