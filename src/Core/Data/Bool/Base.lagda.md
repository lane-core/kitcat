Operations on booleans.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Bool.Base where

open import Core.Type
open import Core.Data.Bool.Type

ind : ∀ {u} (P : Bool → Type u) → P true → P false → ∀ b → P b
ind P t f true  = t
ind P t f false = f
{-# INLINE ind #-}

not : Bool → Bool
not true  = false
not false = true
{-# INLINE not #-}

and : Bool → Bool → Bool
and true  b = b
and false b = false
{-# INLINE and #-}

_&&_ : Bool → Bool → Bool
_&&_ = and
{-# INLINE _&&_ #-}
infixr 6 _&&_

or : Bool → Bool → Bool
or true  b = true
or false b = b
{-# INLINE or #-}

_||_ : Bool → Bool → Bool
_||_ = or
{-# INLINE _||_ #-}
infixr 5 _||_

xor : Bool → Bool → Bool
xor true  true  = false
xor true  false = true
xor false true  = true
xor false false = false
{-# INLINE xor #-}

implies : Bool → Bool → Bool
implies false _ = true
implies true  b = b
{-# INLINE implies #-}

if-then-else : ∀ {u} {@0 P : Bool → Type u} (b : Bool) → P true → P false → P b
if-then-else true  x y = x
if-then-else false x y = y
{-# INLINE if-then-else #-}

```
