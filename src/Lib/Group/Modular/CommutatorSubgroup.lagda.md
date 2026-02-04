Commutator subgroup of the modular group PSL(2,Z).

Adapted from TypeTopology, `Groups.ModularGroup.CommutatorSubgroup`
(Todd Waugh Ambridge). Defines the commutator bracket, the
commutator subgroup as the kernel of the abelianization map, and
proves that every commutator lies in this kernel.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.CommutatorSubgroup where

open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Kan using (_∙_)
open import Core.Type using (Type; 0ℓ)

open import Lib.Group.Modular.Abelianization
open import Lib.Group.Modular.Multiplication
open import Lib.Group.Modular.Inverse
open import Lib.Group.Modular.Type

private
  _≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
          → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ∙ q

  _∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
  x ∎ = refl

  infixr 2 _≡⟨_⟩_
  infix  3 _∎
```


## The commutator bracket

The group-theoretic commutator of two elements.

```agda
[_,_] : PSL2Z → PSL2Z → PSL2Z
[ x , y ] = (x · y) · (inv x · inv y)
```


## Membership in the commutator subgroup

An element belongs to the commutator subgroup when it lies in the
kernel of the abelianization map.

```agda
is-in-commutator : PSL2Z → Type 0ℓ
is-in-commutator g = ab g ≡ 0ᴬ
```


## Commutators are in the kernel

The key observation is that `[x,y] = (x · y) · inv (y · x)` via
`inv-product`, so `ab [x,y] = ab (x·y) +ᴬ ab (inv (y·x))`. By
`ab-commutative` the first summand equals `ab (y·x)`, and then
`ab-hom` applied to `·-inv-right` shows the sum vanishes.

```agda
private
  ab-cancel-right
    : (z : PSL2Z) → ab z +ᴬ ab (inv z) ≡ 0ᴬ
  ab-cancel-right z =
    sym (ab-hom z (inv z)) ∙ ap ab (·-inv-right z)

commutator-in-kernel
  : (x y : PSL2Z) → is-in-commutator [ x , y ]
commutator-in-kernel x y =
  ab ((x · y) · (inv x · inv y))
    ≡⟨ ap (λ w → ab ((x · y) · w))
         (sym (inv-product y x)) ⟩
  ab ((x · y) · inv (y · x))
    ≡⟨ ab-hom (x · y) (inv (y · x)) ⟩
  ab (x · y) +ᴬ ab (inv (y · x))
    ≡⟨ ap (_+ᴬ ab (inv (y · x)))
         (ab-commutative x y) ⟩
  ab (y · x) +ᴬ ab (inv (y · x))
    ≡⟨ ab-cancel-right (y · x) ⟩
  0ᴬ
    ∎
```
