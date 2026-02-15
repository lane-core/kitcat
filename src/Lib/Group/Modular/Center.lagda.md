The center of PSL(2,Z) is trivial.

We show that the only element of PSL(2,Z) commuting with every other
element is the identity E.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Center where

open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Type using (Type; 0ℓ; _∘_)
open import Core.Kan using (_∙_)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Data.Empty using (⊥; ex-falso)
open import Core.Path using (_≢_)

open import Lib.Group.Modular.Multiplication
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


## Centrality

An element g is central if it commutes with every element.

```agda
is-central : PSL2Z → Type 0ℓ
is-central g = (h : PSL2Z) → g · h ≡ h · g
```


## S and R do not commute

Under `--erased-cubical`, `S · R` reduces definitionally to `SR`
since `S = η e₁` and gen-iter on `η e₁` applies `s`. However,
`R · S` does not reduce definitionally because `R = θ (r+ e₀)` and
gen-iter on a `θ`-form goes through `subst`.

```agda
R·S≡RS : R · S ≡ RS
R·S≡RS =
  R · S
    ≡⟨ ap (_· S) (sym (r-η e₀)) ⟩
  (r E) · S
    ≡⟨ ·-r-left E S ⟩
  r (E · S)
    ∎

SR-is-not-RS : SR ≢ RS
SR-is-not-RS = η-is-not-θ (cross (r+ e₀)) (r+ e₁)

S-and-R-dont-commute : S · R ≢ R · S
S-and-R-dont-commute p = SR-is-not-RS (p ∙ R·S≡RS)
```


## Component analysis: multiplication by S

These mutually recursive functions show that multiplying an `η`-form
by S stays in `η`, and multiplying a `θ`-form by S stays in `θ`.

```agda
η·S-in-η : (se : S-edge) → Σ se' ∶ S-edge , (η se) · S ≡ η se'
θ·S-in-θ : (re : R-edge) → Σ re' ∶ R-edge , (θ re) · S ≡ θ re'

η·S-in-η e₀ = e₁ , refl
η·S-in-η e₁ = e₀ , refl
η·S-in-η (cross re) = cross re' , proof where
  re' : R-edge
  re' = fst (θ·S-in-θ re)

  proof : (s∙ re) · S ≡ s∙ re'
  proof =
    (s∙ re) · S
      ≡⟨ ·-s-left (θ re) S ⟩
    s ((θ re) · S)
      ≡⟨ ap s (snd (θ·S-in-θ re)) ⟩
    s∙ re'
      ∎

θ·S-in-θ (r+ se) = r+ se' , proof where
  se' : S-edge
  se' = fst (η·S-in-η se)

  proof : (θ (r+ se)) · S ≡ θ (r+ se')
  proof =
    (θ (r+ se)) · S
      ≡⟨ ap (_· S) (sym (r-η se)) ⟩
    (r (η se)) · S
      ≡⟨ ·-r-left (η se) S ⟩
    r ((η se) · S)
      ≡⟨ ap r (snd (η·S-in-η se)) ⟩
    r (η se')
      ≡⟨ r-η se' ⟩
    θ (r+ se')
      ∎

θ·S-in-θ (r- se) = r- se' , proof where
  se' : S-edge
  se' = fst (η·S-in-η se)

  proof : (θ (r- se)) · S ≡ θ (r- se')
  proof =
    (θ (r- se)) · S
      ≡⟨ ap (_· S) (sym (r²-η se)) ⟩
    (r² (η se)) · S
      ≡⟨ ·-r²-left (η se) S ⟩
    r² ((η se) · S)
      ≡⟨ ap r² (snd (η·S-in-η se)) ⟩
    r² (η se')
      ≡⟨ r²-η se' ⟩
    θ (r- se')
      ∎
```


## Component analysis: multiplication by R

The result type for `(θ re) · R`: the outcome is either E, S, or
another `θ`-element.

```agda
data θ·R-result : Type 0ℓ where
  is-E : θ·R-result
  is-S : θ·R-result
  is-θ : R-edge → θ·R-result

θ·R-target : θ·R-result → PSL2Z
θ·R-target is-E      = E
θ·R-target is-S      = S
θ·R-target (is-θ re) = θ re
```

Applying s to a `θ·R-target` always yields an `η`-form. We track
the resulting S-edge explicitly.

```agda
s-of-θ·R-se : θ·R-result → S-edge
s-of-θ·R-se is-E      = e₁
s-of-θ·R-se is-S      = e₀
s-of-θ·R-se (is-θ re) = cross re

s-of-θ·R-correct
  : (t : θ·R-result)
  → s (θ·R-target t) ≡ η (s-of-θ·R-se t)
s-of-θ·R-correct is-E      = refl
s-of-θ·R-correct is-S      = refl
s-of-θ·R-correct (is-θ re) = refl
```


The mutually recursive pair `θ·R-form` and `s∙·R-in-η`. Under
`--erased-cubical`, the `θ`-form multiplication goes through `subst`
so none of the base cases are definitional.

```agda
θ·R-form
  : (re : R-edge)
  → Σ t ∶ θ·R-result , (θ re) · R ≡ θ·R-target t

s∙·R-in-η
  : (re : R-edge)
  → Σ se ∶ S-edge , (s∙ re) · R ≡ η se
```

Base cases for `θ·R-form` at `r+ se`:

```agda
θ·R-form (r+ e₀) = is-θ (r- e₀) , proof where
  proof : R · R ≡ R²
  proof =
    ap (_· R) (sym (r-η e₀)) ∙ ·-r-left (η e₀) R

θ·R-form (r+ e₁) = is-θ (r+ (cross (r+ e₀))) , proof where
  proof : RS · R ≡ θ (r+ (cross (r+ e₀)))
  proof =
    ap (_· R) (sym (r-η e₁)) ∙ ·-r-left (η e₁) R

θ·R-form (r+ (cross re)) = is-θ (r+ se) , proof where
  se : S-edge
  se = fst (s∙·R-in-η re)

  proof : (r∙ (cross re)) · R ≡ θ (r+ se)
  proof =
    (r∙ (cross re)) · R
      ≡⟨ ap (_· R) (sym (r-η (cross re))) ⟩
    (r (s∙ re)) · R
      ≡⟨ ·-r-left (s∙ re) R ⟩
    r ((s∙ re) · R)
      ≡⟨ ap r (snd (s∙·R-in-η re)) ⟩
    r (η se)
      ≡⟨ r-η se ⟩
    θ (r+ se)
      ∎
```

Base cases for `θ·R-form` at `r- se`:

```agda
θ·R-form (r- e₀) = is-E , proof where
  proof : R² · R ≡ E
  proof =
    ap (_· R) (sym (r²-η e₀)) ∙ ·-r²-left (η e₀) R

θ·R-form (r- e₁) = is-θ (r- (cross (r+ e₀))) , proof where
  proof : R²S · R ≡ θ (r- (cross (r+ e₀)))
  proof =
    ap (_· R) (sym (r²-η e₁)) ∙ ·-r²-left (η e₁) R

θ·R-form (r- (cross re)) = is-θ (r- se) , proof where
  se : S-edge
  se = fst (s∙·R-in-η re)

  proof : (r²∙ (cross re)) · R ≡ θ (r- se)
  proof =
    (r²∙ (cross re)) · R
      ≡⟨ ap (_· R) (sym (r²-η (cross re))) ⟩
    (r² (s∙ re)) · R
      ≡⟨ ·-r²-left (s∙ re) R ⟩
    r² ((s∙ re) · R)
      ≡⟨ ap r² (snd (s∙·R-in-η re)) ⟩
    r² (η se)
      ≡⟨ r²-η se ⟩
    θ (r- se)
      ∎
```

The `s∙·R-in-η` function: `(s∙ re) · R` is always an `η`-form.

```agda
s∙·R-in-η re = s-of-θ·R-se t , proof where
  t : θ·R-result
  t = fst (θ·R-form re)

  proof : (s∙ re) · R ≡ η (s-of-θ·R-se t)
  proof =
    (s∙ re) · R
      ≡⟨ ·-s-left (θ re) R ⟩
    s ((θ re) · R)
      ≡⟨ ap s (snd (θ·R-form re)) ⟩
    s (θ·R-target t)
      ≡⟨ s-of-θ·R-correct t ⟩
    η (s-of-θ·R-se t)
      ∎
```


## Computation of R applied to s-forms

A helper showing `R · (s∙ re) ≡ θ (r+ (cross re))`.

```agda
R·s∙ : (re : R-edge) → R · (s∙ re) ≡ θ (r+ (cross re))
R·s∙ re =
  R · (s∙ re)
    ≡⟨ ap (_· (s∙ re)) (sym (r-η e₀)) ⟩
  (r E) · (s∙ re)
    ≡⟨ ·-r-left E (s∙ re) ⟩
  r (E · (s∙ re))
    ≡⟨ r-η (cross re) ⟩
  θ (r+ (cross re))
    ∎
```


## Center is trivial

The main theorem: every central element equals E.

```agda
center-is-trivial : (g : PSL2Z) → is-central g → g ≡ E
center-is-trivial (η e₀) c = refl
center-is-trivial (η e₁) c =
  ex-falso (S-and-R-dont-commute (c R))
center-is-trivial (η (cross re)) c =
  ex-falso (η-is-not-θ se (r+ (cross re)) p) where
    se : S-edge
    se = fst (s∙·R-in-η re)

    p : η se ≡ θ (r+ (cross re))
    p =
      η se
        ≡⟨ sym (snd (s∙·R-in-η re)) ⟩
      (s∙ re) · R
        ≡⟨ c R ⟩
      R · (s∙ re)
        ≡⟨ R·s∙ re ⟩
      θ (r+ (cross re))
        ∎
center-is-trivial (θ re) c =
  ex-falso (θ-is-not-η re' (cross re) p) where
    re' : R-edge
    re' = fst (θ·S-in-θ re)

    p : θ re' ≡ η (cross re)
    p =
      θ re'
        ≡⟨ sym (snd (θ·S-in-θ re)) ⟩
      (θ re) · S
        ≡⟨ c S ⟩
      S · (θ re)
        ∎
```
