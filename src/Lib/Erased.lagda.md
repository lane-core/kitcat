```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Erased where

open import Lib.Type
open import Agda.Builtin.Cubical.Path

private variable
  u : Level
  @0 A : Type u
  @0 P : A → Type u

infixl -1 #0_

record #0_ {u} (@0 A : Type u) : Type u where
  constructor void
  field
    @0 null : A

open #0_ public

module era where
  map : @0 (∀ x → P x) → (x : #0 A) → #0 P (null x)
  map f (void x) .null = f x

  ap : {@0 x y : A} → #0 x ≡ y → void x ≡ void y
  ap (void p) i = void (p i)

  to-stable : #0 A → ¬¬ A
  to-stable (void x) f = ex-falso (f x)
