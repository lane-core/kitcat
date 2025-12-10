```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prop.HLevel where

open import Lib.Type
open import Lib.Data
open import Lib.Path

record is-contr {u} (A : Type u) : Type u where
  constructor contr
  field
    center : A
    paths : (x : A) → center ≡ x

open is-contr public

private variable ℓ : Level

is-prop : Type ℓ → Type ℓ
is-prop A = (x y : A) → x ≡ y

is-set : Type ℓ → Type ℓ
is-set A = (x y : A) → is-prop (x ≡ y)

is-grpd : Type ℓ → Type ℓ
is-grpd A = (x y : A) → is-set (x ≡ y)

is-hlevel : Nat → Type ℓ → Type ℓ
is-hlevel 0 A = is-contr A
is-hlevel 1 A = is-prop A
is-hlevel (suc (suc n)) A = (x y : A) → is-hlevel (suc n) (x ≡ y)

```
