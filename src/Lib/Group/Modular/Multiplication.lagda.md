Multiplication for the modular group PSL(2,Z).

Defines the group operation via generator
iteration, proves compatibility with s and r, right identity, and
associativity.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Multiplication where

open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Type using (Level; Type; 0ℓ)
open import Core.Kan using (_∙_)
open import Core.Transport.Base using (transport-refl)

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


## Multiplication

The group operation is defined by iterating the generators s and r
over the second argument, driven by the structure of the first.

```agda
_·_ : PSL2Z → PSL2Z → PSL2Z
x · y = PSL2Z-gen-iter y s r x

infixl 30 _·_
```


## Left compatibility with s

```agda
·-s-left : (x y : PSL2Z) → (s x) · y ≡ s (x · y)
·-s-left = PSL2Z-ind base-E base-S ind-s ind-r where
  base-E : (y : PSL2Z) → (s E) · y ≡ s (E · y)
  base-E y = refl

  base-S : (y : PSL2Z) → (s S) · y ≡ s (S · y)
  base-S y = sym (s² y)

  ind-s
    : (re : R-edge)
    → ((y : PSL2Z) → (s (θ re)) · y ≡ s ((θ re) · y))
    → (y : PSL2Z) → (s (s∙ re)) · y ≡ s ((s∙ re) · y)
  ind-s re ih y =
    s (s∙ re) · y         ≡⟨ refl ⟩
    (θ re) · y            ≡⟨ sym (s² ((θ re) · y)) ⟩
    s (s ((θ re) · y))    ≡⟨ refl ⟩
    s ((s∙ re) · y)       ∎

  ind-r
    : (d : R-sgn) (se : S-edge)
    → ((y : PSL2Z) → (s (η se)) · y ≡ s ((η se) · y))
    → (y : PSL2Z) → (s (θ step d se)) · y ≡ s ((θ step d se) · y)
  ind-r d se ih y = refl
```


## Left compatibility with r

Under `--erased-cubical`, `subst (λ _ → X) p` does not reduce to
the identity, so several cases that were `refl` in the original
require `transport-refl` adjustments.

```agda
·-r-left : (x y : PSL2Z) → (r x) · y ≡ r (x · y)
·-r-left = PSL2Z-ind base-E base-S ind-s ind-r where
  base-E : (y : PSL2Z) → (r E) · y ≡ r (E · y)
  base-E y = transport-refl (r y)

  base-S : (y : PSL2Z) → (r S) · y ≡ r (S · y)
  base-S y = transport-refl (r (s y))

  ind-s
    : (re : R-edge)
    → ((y : PSL2Z) → (r (θ re)) · y ≡ r ((θ re) · y))
    → (y : PSL2Z) → (r (s∙ re)) · y ≡ r ((s∙ re) · y)
  ind-s re ih y = transport-refl (r (s ((θ re) · y)))

  ind-r
    : (d : R-sgn) (se : S-edge)
    → ((y : PSL2Z) → (r (η se)) · y ≡ r ((η se) · y))
    → (y : PSL2Z) → (r (θ step d se)) · y ≡ r ((θ step d se) · y)
  ind-r cw  se ih y = refl
  ind-r ccw e₀ ih y =
    sym (ap r² (transport-refl (r y)) ∙ r³ y)
  ind-r ccw e₁ ih y =
    sym (ap r² (transport-refl (r (s y))) ∙ r³ (s y))
  ind-r ccw (cross re) ih y =
    sym (ap r² (transport-refl (r (s ((θ re) · y))))
         ∙ r³ (s ((θ re) · y)))
```


## Left compatibility with r-squared

```agda
·-r²-left : (x y : PSL2Z) → (r² x) · y ≡ r² (x · y)
·-r²-left x y =
  (r² x) · y       ≡⟨ ·-r-left (r x) y ⟩
  r ((r x) · y)    ≡⟨ ap r (·-r-left x y) ⟩
  r² (x · y)       ∎
```


## Right identity

```agda
·-E-right : (x : PSL2Z) → x · E ≡ x
·-E-right = PSL2Z-ind base-E base-S ind-s ind-r where
  base-E : E · E ≡ E
  base-E = refl

  base-S : S · E ≡ S
  base-S = refl

  ind-s
    : (re : R-edge) → (θ re) · E ≡ θ re
    → (s∙ re) · E ≡ s∙ re
  ind-s re p = ·-s-left (θ re) E ∙ ap s p

  ind-r
    : (d : R-sgn) (se : S-edge)
    → (η se) · E ≡ η se → (ρ d se) · E ≡ ρ d se
  ind-r cw se p =
    (r∙ se) · E       ≡⟨ ap (_· E) (sym (r-η se)) ⟩
    (r (η se)) · E    ≡⟨ ·-r-left (η se) E ⟩
    r ((η se) · E)    ≡⟨ ap r p ⟩
    r (η se)          ≡⟨ r-η se ⟩
    r∙ se             ∎
  ind-r ccw se p =
    (r²∙ se) · E      ≡⟨ ap (_· E) (sym (r²-η se)) ⟩
    (r² (η se)) · E   ≡⟨ ·-r²-left (η se) E ⟩
    r² ((η se) · E)   ≡⟨ ap r² p ⟩
    r² (η se)         ≡⟨ r²-η se ⟩
    r²∙ se            ∎
```


## Associativity

```agda
·-assoc : (x y z : PSL2Z) → (x · y) · z ≡ x · (y · z)
·-assoc = PSL2Z-ind base-E base-S ind-s ind-r where
  base-E : (y z : PSL2Z) → (E · y) · z ≡ E · (y · z)
  base-E y z = refl

  base-S : (y z : PSL2Z) → (S · y) · z ≡ S · (y · z)
  base-S y z = ·-s-left y z

  ind-s
    : (re : R-edge)
    → ((y z : PSL2Z) → ((θ re) · y) · z ≡ (θ re) · (y · z))
    → (y z : PSL2Z) → ((s∙ re) · y) · z ≡ (s∙ re) · (y · z)
  ind-s re ih y z =
    ((s∙ re) · y) · z          ≡⟨ ap (_· z) (·-s-left (θ re) y) ⟩
    (s ((θ re) · y)) · z       ≡⟨ ·-s-left ((θ re) · y) z ⟩
    s (((θ re) · y) · z)       ≡⟨ ap s (ih y z) ⟩
    s ((θ re) · (y · z))       ≡⟨ sym (·-s-left (θ re) (y · z)) ⟩
    (s∙ re) · (y · z)          ∎

  ind-r
    : (d : R-sgn) (se : S-edge)
    → ((y z : PSL2Z) → ((η se) · y) · z ≡ (η se) · (y · z))
    → (y z : PSL2Z) → ((ρ d se) · y) · z ≡ (ρ d se) · (y · z)
  ind-r cw se ih y z =
    ((r∙ se) · y) · z
      ≡⟨ ap (λ x → (x · y) · z) (sym (r-η se)) ⟩
    ((r (η se)) · y) · z
      ≡⟨ ap (_· z) (·-r-left (η se) y) ⟩
    (r ((η se) · y)) · z
      ≡⟨ ·-r-left ((η se) · y) z ⟩
    r (((η se) · y) · z)
      ≡⟨ ap r (ih y z) ⟩
    r ((η se) · (y · z))
      ≡⟨ sym (·-r-left (η se) (y · z)) ⟩
    (r (η se)) · (y · z)
      ≡⟨ ap (_· (y · z)) (r-η se) ⟩
    (r∙ se) · (y · z)
      ∎
  ind-r ccw se ih y z =
    ((r²∙ se) · y) · z
      ≡⟨ ap (λ x → (x · y) · z) (sym (r²-η se)) ⟩
    ((r² (η se)) · y) · z
      ≡⟨ ap (_· z) (·-r²-left (η se) y) ⟩
    (r² ((η se) · y)) · z
      ≡⟨ ·-r²-left ((η se) · y) z ⟩
    r² (((η se) · y) · z)
      ≡⟨ ap r² (ih y z) ⟩
    r² ((η se) · (y · z))
      ≡⟨ sym (·-r²-left (η se) (y · z)) ⟩
    (r² (η se)) · (y · z)
      ≡⟨ ap (_· (y · z)) (r²-η se) ⟩
    (r²∙ se) · (y · z)
      ∎
```
