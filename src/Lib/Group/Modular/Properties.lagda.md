Properties of the modular group generators.

This module establishes involution and order-3 properties of the generators,
left-cancellation, injectivity of constructors, discreteness, and sethood.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Properties where

open import Core.Type using (Type; 0ℓ; ⊤; tt; _∘_)
open import Core.Base using (_≡_; refl; sym; ap; ap2; is-set)
open import Core.Kan using (_∙_)
open import Core.Data.Sum using (_⊎_; inl; inr)
open import Core.Data.Bool using (Bool; true; false)
open import Core.Data.Dec using (Dec; yes; no; DecEq)
open Dec using (hedberg)
open import Core.Data.Empty using (⊥; ex-falso; ¬_)
open import Core.Path using (_≢_; ⊎-disjoint)
open import Core.Transport.J using (subst)
open import Core.Trait.Eq using (Eq; Discrete)
open import Core.Trait.Trunc using (Trunc; set-trunc)

open import Lib.Group.Modular.Type
open import Lib.Group.Modular.Base
```


## Involution

The generator s is an involution: applying it twice returns the input.

```agda
s² : (x : PSL2Z) → s (s x) ≡ x
s² (η e₀)  = refl
s² (η e₁)  = refl
s² (s∙ re) = refl
s² (θ re)  = refl
```


## Order-3 rotation

The generator r has order 3: applying it three times returns the input.

```agda
r³ : (x : PSL2Z) → r (r (r x)) ≡ x
r³ (η e₀)         = refl
r³ (η e₁)         = refl
r³ (s∙ re)        = refl
r³ (r∙ e₀)        = refl
r³ (r∙ e₁)        = refl
r³ (r∙ cross re)  = refl
r³ (r²∙ e₀)       = refl
r³ (r²∙ e₁)       = refl
r³ (r²∙ cross re) = refl

r²-r : (x : PSL2Z) → r² (r x) ≡ x
r²-r = r³

r-r² : (x : PSL2Z) → r (r² x) ≡ x
r-r² = r³
```


## Refl-based checks

Simple evaluations confirming the generators act correctly on named elements.

```agda
s-E  : s E  ≡ S;   s-E  = refl
s-S  : s S  ≡ E;   s-S  = refl
r-E  : r E  ≡ R;   r-E  = refl
r-R  : r R  ≡ R²;  r-R  = refl
r-R² : r R² ≡ E;   r-R² = refl
r²-E : r² E ≡ R²;  r²-E = refl
r²-R : r² R ≡ E;   r²-R = refl
r²-R² : r² R² ≡ R; r²-R² = refl
```


## Eta-normalization lemmas

How r and r-squared act on eta- and theta-forms.

```agda
r-η : (se : S-edge) → r (η se) ≡ r∙ se
r-η e₀         = refl
r-η e₁         = refl
r-η (cross re) = refl

r²-η : (se : S-edge) → r² (η se) ≡ r²∙ se
r²-η e₀         = refl
r²-η e₁         = refl
r²-η (cross re) = refl

r-θ-r+ : (se : S-edge) → r (θ (r+ se)) ≡ θ (r- se)
r-θ-r+ e₀         = refl
r-θ-r+ e₁         = refl
r-θ-r+ (cross re) = refl

r-θ-r- : (se : S-edge) → r (θ (r- se)) ≡ η se
r-θ-r- e₀         = refl
r-θ-r- e₁         = refl
r-θ-r- (cross re) = refl
```


## Composite lemmas

Properties of two-step compositions involving r and theta.

```agda
r²-θ-r+ : (se : S-edge) → r² (θ (r+ se)) ≡ η se
r²-θ-r+ se = ap r (r-θ-r+ se) ∙ r-θ-r- se

r²-θ-r- : (se : S-edge) → r² (θ (r- se)) ≡ θ (r+ se)
r²-θ-r- se = ap r (r-θ-r- se) ∙ r-η se

sr-η : (se : S-edge) → s (r (η se)) ≡ sr∙ se
sr-η e₀         = refl
sr-η e₁         = refl
sr-η (cross re) = refl

sr²-η : (se : S-edge) → s (r² (η se)) ≡ sr²∙ se
sr²-η e₀         = refl
sr²-η e₁         = refl
sr²-η (cross re) = refl

rs-θ : (re : R-edge) → r (s (θ re)) ≡ rs∙ re
rs-θ (r+ se) = refl
rs-θ (r- se) = refl

r²s-θ : (re : R-edge) → r² (s (θ re)) ≡ r²s∙ re
r²s-θ (r+ se) = refl
r²s-θ (r- se) = refl

srs-θ : (re : R-edge) → s (r (s (θ re))) ≡ s∙ r+ cross re
srs-θ (r+ se) = refl
srs-θ (r- se) = refl

sr²s-θ : (re : R-edge) → s (r² (s (θ re))) ≡ s∙ r- cross re
sr²s-θ (r+ se) = refl
sr²s-θ (r- se) = refl
```


## Cancellation

Left-cancellation for the generators.

```agda
private
  left-cancellable : ∀ {u} {A : Type u} → (A → A) → Type u
  left-cancellable {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

s-lc : left-cancellable s
s-lc {x} {y} p = sym (s² x) ∙ ap s p ∙ s² y

r-lc : left-cancellable r
r-lc {x} {y} p = sym (r³ x) ∙ ap r² p ∙ r³ y

r²-lc : left-cancellable r²
r²-lc = r-lc ∘ r-lc
```


## Private helpers

Retraction functions for injectivity proofs.

```agda
private
  η-helper : PSL2Z → S-edge
  η-helper (η se) = se
  η-helper (θ _)  = e₀

  θ-helper : PSL2Z → R-edge
  θ-helper (η _)  = r+ e₀
  θ-helper (θ re) = re

  cross-helper : S-edge → R-edge
  cross-helper (cross re) = re
  cross-helper e₀         = step false e₀
  cross-helper e₁         = step false e₁

  r-helper : R-edge → S-edge
  r-helper (step _ se) = se

  r-sgn-fn : R-edge → R-sgn
  r-sgn-fn (step d _) = d
```


## Injection cancellation

The constructors eta and theta are left-cancellable.

```agda
η-lc : {x y : S-edge} → η x ≡ η y → x ≡ y
η-lc p = ap η-helper p

θ-lc : {x y : R-edge} → θ x ≡ θ y → x ≡ y
θ-lc p = ap θ-helper p
```


## Discrimination

Eta and theta injections are disjoint, and S differs from E.

```agda
η-is-not-θ : (x : S-edge) (y : R-edge) → η x ≢ θ y
η-is-not-θ _ _ = ⊎-disjoint

θ-is-not-η : (x : R-edge) (y : S-edge) → θ x ≢ η y
θ-is-not-η _ _ p = ⊎-disjoint (sym p)

S-is-not-E : S ≢ E
S-is-not-E p = subst discrim (η-lc p) tt where
  discrim : S-edge → Type 0ℓ
  discrim e₀      = ⊥
  discrim e₁      = ⊤
  discrim (cross _) = ⊥
```


## Decidable equality

Decidable equality for the mutual types S-edge, R-edge, and PSL2Z,
proved by mutual recursion.

```agda
private
  +functor
    : {A B : Type 0ℓ} → (A → B) → (B → A)
    → Dec A → Dec B
  +functor f _ (yes p) = yes (f p)
  +functor _ g (no np) = no (λ b → np (g b))

  cw-is-not-ccw : cw ≢ ccw
  cw-is-not-ccw p = subst discrim p tt where
    discrim : R-sgn → Type 0ℓ
    discrim cw  = ⊤
    discrim ccw = ⊥

  ccw-is-not-cw : ccw ≢ cw
  ccw-is-not-cw p = cw-is-not-ccw (sym p)

R-sgn-is-discrete : DecEq R-sgn
R-sgn-is-discrete cw  cw  = yes refl
R-sgn-is-discrete cw  ccw = no cw-is-not-ccw
R-sgn-is-discrete ccw cw  = no ccw-is-not-cw
R-sgn-is-discrete ccw ccw = yes refl
```

The mutual block declares the three discrete-equality proofs together.

```agda
S-edge-is-discrete : DecEq S-edge
R-edge-is-discrete : DecEq R-edge
PSL2Z-is-discrete  : DecEq PSL2Z
```

S-edge decidable equality: three constructors, nine cases.

```agda
S-edge-is-discrete e₀ e₀ = yes refl
S-edge-is-discrete e₀ e₁ = no λ p → subst d p tt where
  d : S-edge → Type 0ℓ
  d e₀      = ⊤
  d e₁      = ⊥
  d (cross _) = ⊥
S-edge-is-discrete e₀ (cross _) = no λ p → subst d p tt where
  d : S-edge → Type 0ℓ
  d e₀      = ⊤
  d e₁      = ⊥
  d (cross _) = ⊥
S-edge-is-discrete e₁ e₀ = no λ p → subst d p tt where
  d : S-edge → Type 0ℓ
  d e₀      = ⊥
  d e₁      = ⊤
  d (cross _) = ⊥
S-edge-is-discrete e₁ e₁ = yes refl
S-edge-is-discrete e₁ (cross _) = no λ p → subst d p tt where
  d : S-edge → Type 0ℓ
  d e₀      = ⊥
  d e₁      = ⊤
  d (cross _) = ⊥
S-edge-is-discrete (cross _) e₀ = no λ p → subst d p tt where
  d : S-edge → Type 0ℓ
  d e₀      = ⊥
  d e₁      = ⊥
  d (cross _) = ⊤
S-edge-is-discrete (cross _) e₁ = no λ p → subst d p tt where
  d : S-edge → Type 0ℓ
  d e₀      = ⊥
  d e₁      = ⊥
  d (cross _) = ⊤
S-edge-is-discrete (cross re₁) (cross re₂) =
  +functor (ap cross) (λ p → ap cross-helper p)
    (R-edge-is-discrete re₁ re₂)
```

R-edge decidable equality: step is the sole constructor with two fields.

```agda
R-edge-is-discrete (step d₁ se₁) (step d₂ se₂)
  with R-sgn-is-discrete d₁ d₂ | S-edge-is-discrete se₁ se₂
... | yes dp | yes sp = yes (ap2 step dp sp)
... | yes _  | no np  = no λ p → np (ap r-helper p)
... | no np  | _      = no λ p → np (ap r-sgn-fn p)
```

PSL2Z decidable equality: four cases from the sum decomposition.

```agda
PSL2Z-is-discrete (inl se₁) (inl se₂) =
  +functor (ap inl) η-lc (S-edge-is-discrete se₁ se₂)
PSL2Z-is-discrete (inl _) (inr _) = no ⊎-disjoint
PSL2Z-is-discrete (inr _) (inl _) =
  no (λ p → ⊎-disjoint (sym p))
PSL2Z-is-discrete (inr re₁) (inr re₂) =
  +functor (ap inr) θ-lc (R-edge-is-discrete re₁ re₂)
```


## PSL2Z is a set

By Hedberg's theorem, any type with decidable equality is a set.

```agda
PSL2Z-is-set : is-set PSL2Z
PSL2Z-is-set = hedberg PSL2Z-is-discrete
```


## Instances

```agda
instance
  Discrete-PSL2Z : Discrete PSL2Z
  Discrete-PSL2Z .Discrete._≟_ = PSL2Z-is-discrete

  Eq-PSL2Z : Eq PSL2Z
  Eq-PSL2Z = Discrete.discrete-eq Discrete-PSL2Z

  Trunc-PSL2Z : ∀ {k} → Trunc PSL2Z _
  Trunc-PSL2Z {k} = set-trunc PSL2Z-is-set {k}
```
