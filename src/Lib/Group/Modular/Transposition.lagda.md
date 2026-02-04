Transposition automorphism for the modular group PSL(2,Z).

Adapted from TypeTopology, `Groups.ModularGroup.Transposition`
(Todd Waugh Ambridge). Defines the transposition automorphism that
reverses multiplication order, proves it is an involution, and
an anti-homomorphism: `(x · y) ᵀ ≡ (y ᵀ) · (x ᵀ)`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Transposition where

open import Core.Transport.Base using (transport-refl)
open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Type using (Level; Type; _∘_; 0ℓ)
open import Core.Kan using (_∙_)

open import Lib.Group.Modular.Multiplication
open import Lib.Group.Modular.Induction
open import Lib.Group.Modular.Properties
open import Lib.Group.Modular.Base
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


## Transpose

The transposition is an anti-automorphism of PSL(2,Z) that reverses
the order of multiplication. It is defined by mutual recursion on
S-edges and R-edges.

```agda
transpose-η : S-edge → PSL2Z
transpose-θ : R-edge → PSL2Z

transpose-η e₀         = E
transpose-η e₁         = S
transpose-η (cross re) = (transpose-θ re) · S

transpose-θ (r+ se) = (transpose-η se) · SR²S
transpose-θ (r- se) = (transpose-η se) · SRS

_ᵀ : PSL2Z → PSL2Z
(η se) ᵀ = transpose-η se
(θ re) ᵀ = transpose-θ re

infix 32 _ᵀ
```


## Multiplication identities

Under `--erased-cubical`, multiplication at theta-forms involves
`subst` which does not reduce, so these products need explicit
proofs via `transport-refl`.

```agda
private
  SRS·SR²S≡E : SRS · SR²S ≡ E
  SRS·SR²S≡E = ap s (transport-refl S)

  SR²S·SRS≡E : SR²S · SRS ≡ E
  SR²S·SRS≡E = ap (s ∘ r) (transport-refl (r²∙ e₁))

  SR²S·SR²S≡SRS : SR²S · SR²S ≡ SRS
  SR²S·SR²S≡SRS = ap (s ∘ r) (transport-refl S)

  SRS·SRS≡SR²S : SRS · SRS ≡ SR²S
  SRS·SRS≡SR²S = ap s (transport-refl (r²∙ e₁))
```


## Compatibility with s

```agda
transpose-s : (x : PSL2Z) → (s x) ᵀ ≡ x ᵀ · S
transpose-s (η e₀) = refl
transpose-s (η e₁) = refl
transpose-s (sr∙ se) =
  (s (sr∙ se)) ᵀ
    ≡⟨ sym (·-E-right (transpose-θ (r+ se))) ⟩
  transpose-θ (r+ se) · E
    ≡⟨ sym (·-assoc (transpose-θ (r+ se)) S S) ⟩
  (transpose-θ (r+ se) · S) · S
    ∎
transpose-s (sr²∙ se) =
  (s (sr²∙ se)) ᵀ
    ≡⟨ sym (·-E-right (transpose-θ (r- se))) ⟩
  transpose-θ (r- se) · E
    ≡⟨ sym (·-assoc (transpose-θ (r- se)) S S) ⟩
  (transpose-θ (r- se) · S) · S
    ∎
transpose-s (r∙ se)  = refl
transpose-s (r²∙ se) = refl
```


## Compatibility with r

```agda
transpose-r : (x : PSL2Z) → (r x) ᵀ ≡ x ᵀ · SR²S
transpose-r (η e₀)    = refl
transpose-r (η e₁)    = refl
transpose-r (sr∙ se)  = refl
transpose-r (sr²∙ se) = refl
transpose-r (r∙ se)   =
  (r (r∙ se)) ᵀ
    ≡⟨ ap (transpose-η se ·_) (sym SR²S·SR²S≡SRS) ⟩
  transpose-η se · (SR²S · SR²S)
    ≡⟨ sym (·-assoc (transpose-η se) SR²S SR²S) ⟩
  (transpose-η se · SR²S) · SR²S
    ∎
transpose-r (r²∙ se)  =
  (r (r²∙ se)) ᵀ
    ≡⟨ sym (·-E-right (transpose-η se)) ⟩
  transpose-η se · E
    ≡⟨ ap (transpose-η se ·_) (sym SRS·SR²S≡E) ⟩
  transpose-η se · (SRS · SR²S)
    ≡⟨ sym (·-assoc (transpose-η se) SRS SR²S) ⟩
  (transpose-η se · SRS) · SR²S
    ∎
```


## Compatibility with r-squared

```agda
transpose-r² : (x : PSL2Z) → (r² x) ᵀ ≡ x ᵀ · SRS
transpose-r² (η e₀)    = refl
transpose-r² (η e₁)    = refl
transpose-r² (sr∙ se)  = refl
transpose-r² (sr²∙ se) = refl
transpose-r² (r∙ se)   =
  (r² (r∙ se)) ᵀ
    ≡⟨ sym (·-E-right (transpose-η se)) ⟩
  transpose-η se · E
    ≡⟨ ap (transpose-η se ·_) (sym SR²S·SRS≡E) ⟩
  transpose-η se · (SR²S · SRS)
    ≡⟨ sym (·-assoc (transpose-η se) SR²S SRS) ⟩
  (transpose-η se · SR²S) · SRS
    ∎
transpose-r² (r²∙ se)  =
  (r² (r²∙ se)) ᵀ
    ≡⟨ ap _ᵀ (r²-θ-r- se) ⟩
  (r∙ se) ᵀ
    ≡⟨ ap (transpose-η se ·_) (sym SRS·SRS≡SR²S) ⟩
  transpose-η se · (SRS · SRS)
    ≡⟨ sym (·-assoc (transpose-η se) SRS SRS) ⟩
  (transpose-η se · SRS) · SRS
    ∎
```


## Anti-homomorphism

The transposition reverses multiplication:
`(x · y) ᵀ ≡ (y ᵀ) · (x ᵀ)`.

```agda
transpose-product
  : (x y : PSL2Z) → (x · y) ᵀ ≡ (y ᵀ) · (x ᵀ)
transpose-product =
  PSL2Z-ind
    {P = λ x → (y : PSL2Z)
      → (x · y) ᵀ ≡ (y ᵀ) · (x ᵀ)}
    base-E base-S ind-s ind-r
  where
    base-E : (y : PSL2Z)
      → (E · y) ᵀ ≡ (y ᵀ) · (E ᵀ)
    base-E y = sym (·-E-right (y ᵀ))

    base-S : (y : PSL2Z)
      → (S · y) ᵀ ≡ (y ᵀ) · (S ᵀ)
    base-S y = transpose-s y

    ind-s
      : (re : R-edge)
      → ((y : PSL2Z)
        → ((θ re) · y) ᵀ ≡ (y ᵀ) · ((θ re) ᵀ))
      → (y : PSL2Z)
        → ((s∙ re) · y) ᵀ ≡ (y ᵀ) · ((s∙ re) ᵀ)
    ind-s re ih y =
      ((s∙ re) · y) ᵀ
        ≡⟨ ap _ᵀ (·-s-left (θ re) y) ⟩
      (s ((θ re) · y)) ᵀ
        ≡⟨ transpose-s ((θ re) · y) ⟩
      (((θ re) · y) ᵀ) · S
        ≡⟨ ap (_· S) (ih y) ⟩
      ((y ᵀ) · ((θ re) ᵀ)) · S
        ≡⟨ ·-assoc (y ᵀ) ((θ re) ᵀ) S ⟩
      (y ᵀ) · (((θ re) ᵀ) · S)
        ≡⟨ ap ((y ᵀ) ·_) (sym (transpose-s (θ re))) ⟩
      (y ᵀ) · ((s∙ re) ᵀ)
        ∎

    ind-r
      : (d : R-sgn) (se : S-edge)
      → ((y : PSL2Z)
        → ((η se) · y) ᵀ ≡ (y ᵀ) · ((η se) ᵀ))
      → (y : PSL2Z)
        → ((ρ d se) · y) ᵀ ≡ (y ᵀ) · ((ρ d se) ᵀ)
    ind-r cw se ih y =
      ((r∙ se) · y) ᵀ
        ≡⟨ ap (_ᵀ ∘ (_· y)) (sym (r-η se)) ⟩
      ((r (η se)) · y) ᵀ
        ≡⟨ ap _ᵀ (·-r-left (η se) y) ⟩
      (r ((η se) · y)) ᵀ
        ≡⟨ transpose-r ((η se) · y) ⟩
      (((η se) · y) ᵀ) · SR²S
        ≡⟨ ap (_· SR²S) (ih y) ⟩
      ((y ᵀ) · ((η se) ᵀ)) · SR²S
        ≡⟨ ·-assoc (y ᵀ) ((η se) ᵀ) SR²S ⟩
      (y ᵀ) · (((η se) ᵀ) · SR²S)
        ≡⟨ ap ((y ᵀ) ·_) (sym (transpose-r (η se))) ⟩
      (y ᵀ) · ((r (η se)) ᵀ)
        ≡⟨ ap ((y ᵀ) ·_) (ap _ᵀ (r-η se)) ⟩
      (y ᵀ) · ((r∙ se) ᵀ)
        ∎
    ind-r ccw se ih y =
      ((r²∙ se) · y) ᵀ
        ≡⟨ ap (_ᵀ ∘ (_· y)) (sym (r²-η se)) ⟩
      ((r² (η se)) · y) ᵀ
        ≡⟨ ap _ᵀ (·-r²-left (η se) y) ⟩
      (r² ((η se) · y)) ᵀ
        ≡⟨ transpose-r² ((η se) · y) ⟩
      (((η se) · y) ᵀ) · SRS
        ≡⟨ ap (_· SRS) (ih y) ⟩
      ((y ᵀ) · ((η se) ᵀ)) · SRS
        ≡⟨ ·-assoc (y ᵀ) ((η se) ᵀ) SRS ⟩
      (y ᵀ) · (((η se) ᵀ) · SRS)
        ≡⟨ ap ((y ᵀ) ·_) (sym (transpose-r² (η se))) ⟩
      (y ᵀ) · ((r² (η se)) ᵀ)
        ≡⟨ ap ((y ᵀ) ·_) (ap _ᵀ (r²-η se)) ⟩
      (y ᵀ) · ((r²∙ se) ᵀ)
        ∎
```


## Transposition of named elements

Under `--erased-cubical`, `_·_` at theta-forms involves `subst`
which does not reduce, so the transpositions of `SR²S` and `SRS`
need explicit proofs via `transport-refl`.

```agda
private
  SR²S-ᵀ : SR²S ᵀ ≡ R
  SR²S-ᵀ = transport-refl R

  SRS-ᵀ : SRS ᵀ ≡ R²
  SRS-ᵀ = ap r (transport-refl R)
```


## Involution

The transposition is an involution: applying it twice returns the
input. Proved by mutual induction on edges. Under `--erased-cubical`,
the `transpose-product` result at `SR²S` and `SRS` does not reduce
to `r` or `r²` applications, so intermediate steps through
`SR²S-ᵀ` and `SRS-ᵀ` with `·-r-left` and `·-r²-left` are needed.

```agda
transpose-involutive-η
  : (se : S-edge) → transpose-η se ᵀ ≡ η se
transpose-involutive-θ
  : (re : R-edge) → transpose-θ re ᵀ ≡ θ re

transpose-involutive-η e₀ = refl
transpose-involutive-η e₁ = refl
transpose-involutive-η (cross re) =
  ((transpose-θ re) · S) ᵀ
    ≡⟨ transpose-product (transpose-θ re) S ⟩
  s ((transpose-θ re) ᵀ)
    ≡⟨ ap s (transpose-involutive-θ re) ⟩
  η (cross re)
    ∎

transpose-involutive-θ (r+ se) =
  ((transpose-η se) · SR²S) ᵀ
    ≡⟨ transpose-product (transpose-η se) SR²S ⟩
  SR²S ᵀ · (transpose-η se) ᵀ
    ≡⟨ ap (_· (transpose-η se) ᵀ) SR²S-ᵀ ⟩
  R · (transpose-η se) ᵀ
    ≡⟨ ·-r-left E ((transpose-η se) ᵀ) ⟩
  r ((transpose-η se) ᵀ)
    ≡⟨ ap r (transpose-involutive-η se) ⟩
  r (η se)
    ≡⟨ r-η se ⟩
  θ (r+ se)
    ∎

transpose-involutive-θ (r- se) =
  ((transpose-η se) · SRS) ᵀ
    ≡⟨ transpose-product (transpose-η se) SRS ⟩
  SRS ᵀ · (transpose-η se) ᵀ
    ≡⟨ ap (_· (transpose-η se) ᵀ) SRS-ᵀ ⟩
  R² · (transpose-η se) ᵀ
    ≡⟨ ·-r²-left E ((transpose-η se) ᵀ) ⟩
  r² ((transpose-η se) ᵀ)
    ≡⟨ ap r² (transpose-involutive-η se) ⟩
  r² (η se)
    ≡⟨ r²-η se ⟩
  θ (r- se)
    ∎

transpose-involutive : (x : PSL2Z) → (x ᵀ) ᵀ ≡ x
transpose-involutive (η se) = transpose-involutive-η se
transpose-involutive (θ re) = transpose-involutive-θ re
```
