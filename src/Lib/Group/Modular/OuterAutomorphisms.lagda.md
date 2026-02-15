The twist automorphism of PSL(2,Z) is not inner.

We prove that there is no element g of PSL(2,Z)
such that conjugation by g equals the twist automorphism. This shows
that Out(PSL(2,Z)) is nontrivial (isomorphic to Z/2).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.OuterAutomorphisms where

open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Type using (Type; 0ℓ; _∘_)
open import Core.Kan using (_∙_)
open import Core.Data.Sum using (_⊎_; inl; inr)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Data.Empty using (⊥; ex-falso)
open import Core.Path using (_≢_)

open import Lib.Group.Modular.Multiplication
open import Lib.Group.Modular.Inverse
open import Lib.Group.Modular.Properties
open import Lib.Group.Modular.Center
open import Lib.Group.Modular.Twist
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


## Conjugation

Conjugation by g sends x to g * x * g^{-1}.

```agda
conj : PSL2Z → PSL2Z → PSL2Z
conj g x = g · (x · inv g)
```


## Commuting with S

An element g commutes with S when g * S = S * g.

```agda
commutes-with-S : PSL2Z → Type 0ℓ
commutes-with-S g = g · S ≡ S · g
```


## S-centralizer

If g commutes with S, then g is either E or S. The proof analyzes the
eta/theta partition: for eta-forms with a cross, and for all
theta-forms, commuting with S produces a component mismatch.

For the eta (cross re) case: the LHS `(s∙ re) · S` equals
`s ((θ re) · S)` by `·-s-left`. By `θ·S-in-θ`, `(θ re) · S` is a
theta-form, so `s ((θ re) · S)` is an eta-form. The RHS `S · (s∙ re)`
is `s (s (s∙ re)) = s (θ re)` which is `s∙ re`, an eta-form. But the
hypothesis equates `(s∙ re) · S` (an eta-form via the above) with
`S · (s∙ re)` which reduces definitionally. We extract the
contradiction from the component data.

For the theta case: `(θ re) · S` stays in theta by `θ·S-in-θ`,
while `S · (θ re) = s (θ re) = s∙ re` is an eta-form. Contradiction.

```agda
S-centralizer
  : (g : PSL2Z) → commutes-with-S g → (g ≡ E) ⊎ (g ≡ S)
S-centralizer (η e₀) _ = inl refl
S-centralizer (η e₁) _ = inr refl
S-centralizer (η (cross re)) p =
  ex-falso (η-is-not-θ (cross re') re q) where
    re' : R-edge
    re' = fst (θ·S-in-θ re)

    q : η (cross re') ≡ θ re
    q =
      η (cross re')
        ≡⟨ sym (ap s (snd (θ·S-in-θ re))) ⟩
      s ((θ re) · S)
        ≡⟨ sym (·-s-left (θ re) S) ⟩
      (s∙ re) · S
        ≡⟨ p ⟩
      S · (s∙ re)
        ∎
S-centralizer (θ re) p =
  ex-falso (θ-is-not-η re' (cross re) q) where
    re' : R-edge
    re' = fst (θ·S-in-θ re)

    q : θ re' ≡ η (cross re)
    q =
      θ re'
        ≡⟨ sym (snd (θ·S-in-θ re)) ⟩
      (θ re) · S
        ≡⟨ p ⟩
      S · (θ re)
        ∎
```


## Conjugation by E is the identity

```agda
private
  conj-E : (x : PSL2Z) → conj E x ≡ x
  conj-E x = ·-E-right x
```


## Conjugation by S applied to R

We compute conj S R = S * (R * inv S) = S * (R * S) = SRS.

```agda
private
  conj-S-R : conj S R ≡ SRS
  conj-S-R =
    S · (R · S)
      ≡⟨ ap (S ·_) R·S≡RS ⟩
    S · RS
      ≡⟨ ·-s-left (θ (r+ e₁)) E ⟩
    s (RS · E)
      ≡⟨ ap s (·-E-right RS) ⟩
    SRS
      ∎
```


## Discrimination lemmas

SRS is an eta-form, R-squared is a theta-form; R and R-squared are
distinct theta-forms.

```agda
private
  SRS-is-not-R² : SRS ≢ R²
  SRS-is-not-R² = η-is-not-θ (cross (r+ e₁)) (r- e₀)

  R-is-not-R² : R ≢ R²
  R-is-not-R² p = cw≢ccw (ap r-sgn (θ-lc p)) where
    r-sgn : R-edge → R-sgn
    r-sgn (step d _) = d

    cw≢ccw : cw ≢ ccw
    cw≢ccw q = S-is-not-E (ap decode q) where
      decode : R-sgn → PSL2Z
      decode cw  = S
      decode ccw = E
```


## Twist is not inner

If twist equals conjugation by some g, then from twist-s and
specializing to x = E, we obtain g * S * g^{-1} = S, from which
g commutes with S. The S-centralizer then forces g to be E or S,
and both cases lead to contradiction.

```agda
twist-not-inner
  : (g : PSL2Z) → ((x : PSL2Z) → twist x ≡ conj g x) → ⊥
twist-not-inner g h = elim (S-centralizer g g-comm-S) where
  conj-g-s : (x : PSL2Z) → conj g (s x) ≡ s (conj g x)
  conj-g-s x = sym (h (s x)) ∙ twist-s x ∙ ap s (h x)

  g·S·g⁻¹≡S : g · (S · inv g) ≡ S
  g·S·g⁻¹≡S =
    g · (S · inv g)
      ≡⟨ conj-g-s E ⟩
    s (g · inv g)
      ≡⟨ ap s (·-inv-right g) ⟩
    S
      ∎

  g-comm-S : commutes-with-S g
  g-comm-S =
    g · S
      ≡⟨ sym (·-E-right (g · S)) ⟩
    (g · S) · E
      ≡⟨ ap ((g · S) ·_) (sym (·-inv-left g)) ⟩
    (g · S) · (inv g · g)
      ≡⟨ sym (·-assoc (g · S) (inv g) g) ⟩
    ((g · S) · inv g) · g
      ≡⟨ ap (_· g) (·-assoc g S (inv g)) ⟩
    (g · (S · inv g)) · g
      ≡⟨ ap (_· g) g·S·g⁻¹≡S ⟩
    S · g
      ∎

  elim : (g ≡ E) ⊎ (g ≡ S) → ⊥
  elim (inl g≡E) = R-is-not-R²
    (sym (conj-E R)
    ∙ ap (λ z → conj z R) (sym g≡E)
    ∙ sym (h R))
  elim (inr g≡S) = SRS-is-not-R²
    (sym conj-S-R
    ∙ ap (λ z → conj z R) (sym g≡S)
    ∙ sym (h R))
```
