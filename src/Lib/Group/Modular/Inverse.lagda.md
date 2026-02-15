Inverse for the modular group PSL(2,Z).

Defines the group inverse via mutual recursion
on edges, proves left and right inverse laws, involution of inv,
generator interaction, and the anti-homomorphism property.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Inverse where

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


## Right-multiplication by generators

These are defined as generator iteration and used throughout the
inverse proofs.

```agda
_·S : PSL2Z → PSL2Z
_·S = PSL2Z-gen-iter S s r

_·R² : PSL2Z → PSL2Z
_·R² = PSL2Z-gen-iter R² s r

_·R : PSL2Z → PSL2Z
_·R = PSL2Z-gen-iter R s r
```


## Inverse

The inverse is defined by mutual recursion on S-edges and R-edges.
On the identity and involution it is trivial; on rotations it
composes with the appropriate inverse rotation.

```agda
inv-η : S-edge → PSL2Z
inv-θ : R-edge → PSL2Z

inv-η e₀         = E
inv-η e₁         = S
inv-η (cross re) = (inv-θ re) ·S

inv-θ (r+ se) = (inv-η se) ·R²
inv-θ (r- se) = (inv-η se) ·R

inv : PSL2Z → PSL2Z
inv (η se) = inv-η se
inv (θ re) = inv-θ re
```


## Inverse checks

```agda
private
  inv-E  : inv E ≡ E;   inv-E  = refl
  inv-S  : inv S ≡ S;   inv-S  = refl
  inv-R  : inv R ≡ R²;  inv-R  = refl
  inv-R² : inv R² ≡ R;  inv-R² = refl
```


## Right-multiplication involutions

Applying `_·S` twice is the identity. The base cases are
definitional; the inductive cases use compatibility lemmas.

```agda
·S-·S : (x : PSL2Z) → (x ·S) ·S ≡ x
·S-·S = PSL2Z-ind base-E base-S ind-s ind-r where
  base-E : (E ·S) ·S ≡ E
  base-E = refl

  base-S : (S ·S) ·S ≡ S
  base-S = refl

  ind-s
    : (re : R-edge) → ((θ re) ·S) ·S ≡ θ re
    → ((s∙ re) ·S) ·S ≡ s∙ re
  ind-s re p =
    ap (_·S) (·-s-left (θ re) S)
    ∙ ·-s-left ((θ re) ·S) S
    ∙ ap s p

  ind-r
    : (d : R-sgn) (se : S-edge)
    → ((η se) ·S) ·S ≡ η se
    → ((ρ d se) ·S) ·S ≡ ρ d se
  ind-r cw se p =
    ((r∙ se) ·S) ·S
      ≡⟨ ap (λ x → (x ·S) ·S) (sym (r-η se)) ⟩
    ((r (η se)) ·S) ·S
      ≡⟨ ap (_·S) (·-r-left (η se) S) ⟩
    (r ((η se) ·S)) ·S
      ≡⟨ ·-r-left ((η se) ·S) S ⟩
    r (((η se) ·S) ·S)
      ≡⟨ ap r p ⟩
    r (η se)
      ≡⟨ r-η se ⟩
    r∙ se
      ∎
  ind-r ccw se p =
    ((r²∙ se) ·S) ·S
      ≡⟨ ap (λ x → (x ·S) ·S) (sym (r²-η se)) ⟩
    ((r² (η se)) ·S) ·S
      ≡⟨ ap (_·S) (·-r²-left (η se) S) ⟩
    (r² ((η se) ·S)) ·S
      ≡⟨ ·-r²-left ((η se) ·S) S ⟩
    r² (((η se) ·S) ·S)
      ≡⟨ ap r² p ⟩
    r² (η se)
      ≡⟨ r²-η se ⟩
    r²∙ se
      ∎
```

Applying `_·R` then `_·R²` is the identity. Under `--erased-cubical`
the `subst` in `PSL2Z-gen-ind` does not reduce on constant families,
so the base cases require `·-r-left` / `·-r²-left` rather than `refl`.

```agda
·R-·R² : (x : PSL2Z) → (x ·R) ·R² ≡ x
·R-·R² = PSL2Z-ind base-E base-S ind-s ind-r where
  base-E : (E ·R) ·R² ≡ E
  base-E = ·-r-left E R²

  base-S : (S ·R) ·R² ≡ S
  base-S = ap s (·-r-left E R²)

  ind-s
    : (re : R-edge) → ((θ re) ·R) ·R² ≡ θ re
    → ((s∙ re) ·R) ·R² ≡ s∙ re
  ind-s re p =
    ap (_·R²) (·-s-left (θ re) R)
    ∙ ·-s-left ((θ re) ·R) R²
    ∙ ap s p

  ind-r
    : (d : R-sgn) (se : S-edge)
    → ((η se) ·R) ·R² ≡ η se
    → ((ρ d se) ·R) ·R² ≡ ρ d se
  ind-r cw se p =
    ((r∙ se) ·R) ·R²
      ≡⟨ ap (λ x → (x ·R) ·R²) (sym (r-η se)) ⟩
    ((r (η se)) ·R) ·R²
      ≡⟨ ap (_·R²) (·-r-left (η se) R) ⟩
    (r ((η se) ·R)) ·R²
      ≡⟨ ·-r-left ((η se) ·R) R² ⟩
    r (((η se) ·R) ·R²)
      ≡⟨ ap r p ⟩
    r (η se)
      ≡⟨ r-η se ⟩
    r∙ se
      ∎
  ind-r ccw se p =
    ((r²∙ se) ·R) ·R²
      ≡⟨ ap (λ x → (x ·R) ·R²) (sym (r²-η se)) ⟩
    ((r² (η se)) ·R) ·R²
      ≡⟨ ap (_·R²) (·-r²-left (η se) R) ⟩
    (r² ((η se) ·R)) ·R²
      ≡⟨ ·-r²-left ((η se) ·R) R² ⟩
    r² (((η se) ·R) ·R²)
      ≡⟨ ap r² p ⟩
    r² (η se)
      ≡⟨ r²-η se ⟩
    r²∙ se
      ∎
```

Applying `_·R²` then `_·R` is the identity.

```agda
·R²-·R : (x : PSL2Z) → (x ·R²) ·R ≡ x
·R²-·R = PSL2Z-ind base-E base-S ind-s ind-r where
  base-E : (E ·R²) ·R ≡ E
  base-E = ·-r²-left E R

  base-S : (S ·R²) ·R ≡ S
  base-S = ap s (·-r²-left E R)

  ind-s
    : (re : R-edge) → ((θ re) ·R²) ·R ≡ θ re
    → ((s∙ re) ·R²) ·R ≡ s∙ re
  ind-s re p =
    ap (_·R) (·-s-left (θ re) R²)
    ∙ ·-s-left ((θ re) ·R²) R
    ∙ ap s p

  ind-r
    : (d : R-sgn) (se : S-edge)
    → ((η se) ·R²) ·R ≡ η se
    → ((ρ d se) ·R²) ·R ≡ ρ d se
  ind-r cw se p =
    ((r∙ se) ·R²) ·R
      ≡⟨ ap (λ x → (x ·R²) ·R) (sym (r-η se)) ⟩
    ((r (η se)) ·R²) ·R
      ≡⟨ ap (_·R) (·-r-left (η se) R²) ⟩
    (r ((η se) ·R²)) ·R
      ≡⟨ ·-r-left ((η se) ·R²) R ⟩
    r (((η se) ·R²) ·R)
      ≡⟨ ap r p ⟩
    r (η se)
      ≡⟨ r-η se ⟩
    r∙ se
      ∎
  ind-r ccw se p =
    ((r²∙ se) ·R²) ·R
      ≡⟨ ap (λ x → (x ·R²) ·R) (sym (r²-η se)) ⟩
    ((r² (η se)) ·R²) ·R
      ≡⟨ ap (_·R) (·-r²-left (η se) R²) ⟩
    (r² ((η se) ·R²)) ·R
      ≡⟨ ·-r²-left ((η se) ·R²) R ⟩
    r² (((η se) ·R²) ·R)
      ≡⟨ ap r² p ⟩
    r² (η se)
      ≡⟨ r²-η se ⟩
    r²∙ se
      ∎
```

Squaring `_·R²` yields `_·R`, and squaring `_·R` yields `_·R²`.

```agda
R²-R²-is-R : R² · R² ≡ R
R²-R²-is-R = ·-r²-left E R²

·R²-·R² : (x : PSL2Z) → (x ·R²) ·R² ≡ x ·R
·R²-·R² x =
  ·-assoc x R² R² ∙ ap (x ·_) R²-R²-is-R

R-R-is-R² : R · R ≡ R²
R-R-is-R² = ·-r-left E R

·R-·R : (x : PSL2Z) → (x ·R) ·R ≡ x ·R²
·R-·R x =
  ·-assoc x R R ∙ ap (x ·_) R-R-is-R²
```


## Left inverse

```agda
private
  r²r-η : (se : S-edge) → r² (r (η se)) ≡ η se
  r²r-η e₀         = refl
  r²r-η e₁         = refl
  r²r-η (cross re) = refl

  rr²-η : (se : S-edge) → r (r² (η se)) ≡ η se
  rr²-η e₀         = refl
  rr²-η e₁         = refl
  rr²-η (cross re) = refl

·-inv-left-η : (se : S-edge) → (inv-η se) · (η se) ≡ E
·-inv-left-θ : (re : R-edge) → (inv-θ re) · (θ re) ≡ E

·-inv-left-η e₀ = refl
·-inv-left-η e₁ = s² E
·-inv-left-η (cross re) =
  ((inv-θ re) ·S) · s (θ re)
    ≡⟨ ·-assoc (inv-θ re) S (s (θ re)) ⟩
  (inv-θ re) · (S · s (θ re))
    ≡⟨ ap ((inv-θ re) ·_) (s² (θ re)) ⟩
  (inv-θ re) · (θ re)
    ≡⟨ ·-inv-left-θ re ⟩
  E
    ∎

·-inv-left-θ (r+ se) =
  ((inv-η se) ·R²) · (θ (r+ se))
    ≡⟨ ap (((inv-η se) ·R²) ·_) (sym (r-η se)) ⟩
  ((inv-η se) ·R²) · r (η se)
    ≡⟨ ·-assoc (inv-η se) R² (r (η se)) ⟩
  (inv-η se) · (R² · r (η se))
    ≡⟨ ap ((inv-η se) ·_)
         (·-r²-left E (r (η se)) ∙ r²r-η se) ⟩
  (inv-η se) · (η se)
    ≡⟨ ·-inv-left-η se ⟩
  E
    ∎

·-inv-left-θ (r- se) =
  ((inv-η se) ·R) · (θ (r- se))
    ≡⟨ ap (((inv-η se) ·R) ·_) (sym (r²-η se)) ⟩
  ((inv-η se) ·R) · r² (η se)
    ≡⟨ ·-assoc (inv-η se) R (r² (η se)) ⟩
  (inv-η se) · (R · r² (η se))
    ≡⟨ ap ((inv-η se) ·_)
         (·-r-left E (r² (η se)) ∙ rr²-η se) ⟩
  (inv-η se) · (η se)
    ≡⟨ ·-inv-left-η se ⟩
  E
    ∎

·-inv-left : (x : PSL2Z) → (inv x) · x ≡ E
·-inv-left (η se) = ·-inv-left-η se
·-inv-left (θ re) = ·-inv-left-θ re
```


## Right inverse

```agda
·-inv-right-η : (se : S-edge) → (η se) · (inv-η se) ≡ E
·-inv-right-θ : (re : R-edge) → (θ re) · (inv-θ re) ≡ E

·-inv-right-η e₀ = refl
·-inv-right-η e₁ = s² E
·-inv-right-η (cross re) =
  s (θ re) · ((inv-θ re) ·S)
    ≡⟨ ·-s-left (θ re) ((inv-θ re) ·S) ⟩
  s ((θ re) · ((inv-θ re) ·S))
    ≡⟨ ap s (sym (·-assoc (θ re) (inv-θ re) S)) ⟩
  s (((θ re) · (inv-θ re)) · S)
    ≡⟨ ap (λ z → s (z · S)) (·-inv-right-θ re) ⟩
  E
    ∎

·-inv-right-θ (r+ se) =
  (θ (r+ se)) · ((inv-η se) ·R²)
    ≡⟨ ap (_· ((inv-η se) ·R²)) (sym (r-η se)) ⟩
  r (η se) · ((inv-η se) ·R²)
    ≡⟨ ·-r-left (η se) ((inv-η se) ·R²) ⟩
  r ((η se) · ((inv-η se) ·R²))
    ≡⟨ ap r (sym (·-assoc (η se) (inv-η se) R²)) ⟩
  r (((η se) · (inv-η se)) · R²)
    ≡⟨ I ⟩
  r R²
    ≡⟨ r-R² ⟩
  E
    ∎
  where
    I = ap (λ z → r (z · R²)) (·-inv-right-η se)

·-inv-right-θ (r- se) =
  (θ (r- se)) · ((inv-η se) ·R)
    ≡⟨ ap (_· ((inv-η se) ·R)) (sym (r²-η se)) ⟩
  r² (η se) · ((inv-η se) ·R)
    ≡⟨ ·-r²-left (η se) ((inv-η se) ·R) ⟩
  r² ((η se) · ((inv-η se) ·R))
    ≡⟨ ap r² (sym (·-assoc (η se) (inv-η se) R)) ⟩
  r² (((η se) · (inv-η se)) · R)
    ≡⟨ I ⟩
  r² R
    ≡⟨ ap r r-R ∙ r-R² ⟩
  E
    ∎
  where
    I = ap (λ z → r² (z · R)) (·-inv-right-η se)

·-inv-right : (x : PSL2Z) → x · (inv x) ≡ E
·-inv-right (η se) = ·-inv-right-η se
·-inv-right (θ re) = ·-inv-right-θ re
```


## Involution

The inverse is an involution: `inv (inv x) ≡ x`.

```agda
inv-involute : (x : PSL2Z) → inv (inv x) ≡ x
inv-involute x =
  inv (inv x)
    ≡⟨ sym (·-E-right (inv (inv x))) ⟩
  (inv (inv x)) · E
    ≡⟨ ap ((inv (inv x)) ·_) (sym (·-inv-left x)) ⟩
  (inv (inv x)) · ((inv x) · x)
    ≡⟨ sym (·-assoc (inv (inv x)) (inv x) x) ⟩
  ((inv (inv x)) · (inv x)) · x
    ≡⟨ ap (_· x) (·-inv-left (inv x)) ⟩
  x
    ∎
```


## Generator interaction

How `inv` commutes with the generators s, r, and r-squared.

```agda
inv-s : (x : PSL2Z) → inv (s x) ≡ (inv x) · S
inv-s (η e₀) = refl
inv-s (η e₁) = refl
inv-s (sr∙ se) = sym (·S-·S (inv-θ (r+ se)))
inv-s (sr²∙ se) = sym (·S-·S (inv-θ (r- se)))
inv-s (r∙ se) = refl
inv-s (r²∙ se) = refl

inv-r : (x : PSL2Z) → inv (r x) ≡ (inv x) · R²
inv-r (η e₀)    = refl
inv-r (η e₁)    = refl
inv-r (sr∙ se)  = refl
inv-r (sr²∙ se) = refl
inv-r (r∙ se)   =
  ap inv (r-θ-r+ se) ∙ sym (·R²-·R² (inv-η se))
inv-r (r²∙ se)  =
  ap inv (r-θ-r- se) ∙ sym (·R-·R² (inv-η se))

inv-r² : (x : PSL2Z) → inv (r² x) ≡ (inv x) · R
inv-r² (η e₀)    = refl
inv-r² (η e₁)    = refl
inv-r² (sr∙ se)  = refl
inv-r² (sr²∙ se) = refl
inv-r² (r∙ se)   =
  ap inv (r²-θ-r+ se) ∙ sym (·R²-·R (inv-η se))
inv-r² (r²∙ se)  =
  ap inv (r²-θ-r- se) ∙ sym (·R-·R (inv-η se))
```


## Anti-homomorphism

The inverse reverses multiplication: `inv (x · y) ≡ (inv y) · (inv x)`.

```agda
inv-product : (x y : PSL2Z) → inv (x · y) ≡ (inv y) · (inv x)
inv-product =
  PSL2Z-ind
    {P = λ x → (y : PSL2Z) → inv (x · y) ≡ (inv y) · (inv x)}
    base-E base-S ind-s ind-r
  where
    base-E : (y : PSL2Z) → inv (E · y) ≡ (inv y) · (inv E)
    base-E y = sym (·-E-right (inv y))

    base-S : (y : PSL2Z) → inv (S · y) ≡ (inv y) · (inv S)
    base-S y = inv-s y

    ind-s
      : (re : R-edge)
      → ((y : PSL2Z) → inv ((θ re) · y) ≡ (inv y) · (inv (θ re)))
      → (y : PSL2Z) → inv ((s∙ re) · y) ≡ (inv y) · (inv (s∙ re))
    ind-s re ih y =
      inv ((s∙ re) · y)
        ≡⟨ ap inv (·-s-left (θ re) y) ⟩
      inv (s ((θ re) · y))
        ≡⟨ inv-s ((θ re) · y) ⟩
      (inv ((θ re) · y)) · S
        ≡⟨ ap (_· S) (ih y) ⟩
      ((inv y) · (inv (θ re))) · S
        ≡⟨ ·-assoc (inv y) (inv (θ re)) S ⟩
      (inv y) · ((inv (θ re)) · S)
        ≡⟨ ap ((inv y) ·_) (sym (inv-s (θ re))) ⟩
      (inv y) · (inv (s∙ re))
        ∎

    ind-r
      : (d : R-sgn) (se : S-edge)
      → ((y : PSL2Z)
        → inv ((η se) · y) ≡ (inv y) · (inv (η se)))
      → (y : PSL2Z)
        → inv ((ρ d se) · y) ≡ (inv y) · (inv (ρ d se))
    ind-r cw se ih y =
      inv ((r∙ se) · y)
        ≡⟨ ap (inv ∘ (_· y)) (sym (r-η se)) ⟩
      inv ((r (η se)) · y)
        ≡⟨ ap inv (·-r-left (η se) y) ⟩
      inv (r ((η se) · y))
        ≡⟨ inv-r ((η se) · y) ⟩
      (inv ((η se) · y)) · R²
        ≡⟨ ap (_· R²) (ih y) ⟩
      ((inv y) · (inv (η se))) · R²
        ≡⟨ ·-assoc (inv y) (inv (η se)) R² ⟩
      (inv y) · ((inv (η se)) · R²)
        ≡⟨ ap ((inv y) ·_) (sym (inv-r (η se))) ⟩
      (inv y) · (inv (r (η se)))
        ≡⟨ ap ((inv y) ·_) (ap inv (r-η se)) ⟩
      (inv y) · (inv (r∙ se))
        ∎
    ind-r ccw se ih y =
      inv ((r²∙ se) · y)
        ≡⟨ ap (inv ∘ (_· y)) (sym (r²-η se)) ⟩
      inv ((r² (η se)) · y)
        ≡⟨ ap inv (·-r²-left (η se) y) ⟩
      inv (r² ((η se) · y))
        ≡⟨ inv-r² ((η se) · y) ⟩
      (inv ((η se) · y)) · R
        ≡⟨ ap (_· R) (ih y) ⟩
      ((inv y) · (inv (η se))) · R
        ≡⟨ ·-assoc (inv y) (inv (η se)) R ⟩
      (inv y) · ((inv (η se)) · R)
        ≡⟨ ap ((inv y) ·_) (sym (inv-r² (η se))) ⟩
      (inv y) · (inv (r² (η se)))
        ≡⟨ ap ((inv y) ·_) (ap inv (r²-η se)) ⟩
      (inv y) · (inv (r²∙ se))
        ∎
```
