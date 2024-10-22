Lane Biocini
Ulf Norell (code taken from agda-prelude)
Oct 12th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Pi.Base where

infixr -20 _$_ _$′_
infixl -10 id

open import Lib.Prim
open import Lib.Pi.Type
open import Lib.Trait.Cut

id : ∀ {u} {A : u type} → A → A
id = λ x → x
{-# INLINE id #-}

syntax id {A = A} x = x ꞉ A type

const : ∀ {u v} {A : u type} {B : v type} → A → B → A
const x _ = x
{-# INLINE const #-}

flip : ∀ {u v w} {A : u type} {B : v type} {C : A → B → w type} → (∀ x y → C x y) → ∀ y x → C x y
flip f x y = f y x
{-# INLINE flip #-}

_$_ : ∀ {u v} {A : u type} {B : A → v type} → (∀ x → B x) → ∀ x → B x
f $ x = f x
{-# INLINE _$_ #-}

_$′_ : ∀ {u v}{A : u type} {B : v type} → (A → B) → A → B
f $′ x = f x
{-# INLINE _$′_ #-}

it : ∀ {u} {A : u type} {{x : A}} → A
it {{x}} = x
{-# INLINE it #-}

as-instance : ∀ {u v} {A : u type} {B : A → v type} (x : A) → (∀ {{x}} → B x) → B x
as-instance x f = f {{x}}
{-# INLINE as-instance #-}

-- Can be used to force normalisation at compile time.
static : ∀ {u} {A : u type} → A → A
static x = x
{-# STATIC static #-}
