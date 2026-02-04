Calkin-Wilf generators and commutator properties of PSL(2,Z).

The Calkin-Wilf tree generators L and R-CW correspond to the
group elements sr-squared and sr respectively. This module proves
basic properties of the commutator bracket, including that the
commutator of S and R is nontrivial.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.CalkinWilf where

open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Type using (Type; 0ℓ; ⊤; tt)
open import Core.Kan using (_∙_)
open import Core.Data.Empty using (⊥)
open import Core.Path using (_≢_)
open import Core.Transport.Base using (transport-refl)
open import Core.Transport.J using (subst)

open import Lib.Group.Modular.CommutatorSubgroup
open import Lib.Group.Modular.Multiplication
open import Lib.Group.Modular.Inverse
open import Lib.Group.Modular.Properties
open import Lib.Group.Modular.Base
open import Lib.Group.Modular.Type
open import Lib.Group.Modular.Depth

private
  _≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
          → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ∙ q

  _∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
  x ∎ = refl

  infixr 2 _≡⟨_⟩_
  infix  3 _∎
```


## Calkin-Wilf generators

The left and right moves in the Calkin-Wilf tree correspond to the
compositions sr-squared and sr.

```agda
L : PSL2Z → PSL2Z
L = sr²

R-CW : PSL2Z → PSL2Z
R-CW = sr
```


## Commutator of S and R

The commutator `[S,R] = (S · R) · (inv S · inv R)` simplifies
because `inv S = S` and `inv R = R²`, and the products
`S · R = SR` and `S · R² = SR²` hold definitionally.

```agda
S·R≡SR : S · R ≡ SR
S·R≡SR = refl

S·R²≡SR² : S · R² ≡ SR²
S·R²≡SR² = refl

[S,R]-expand : [ S , R ] ≡ SR · SR²
[S,R]-expand = refl
```


## Multiplication of named elements

Computing products of small elements, with transport-refl
adjustments where the `subst` in `PSL2Z-gen-ind` blocks reduction.

```agda
R·S≡RS : R · S ≡ RS
R·S≡RS = transport-refl _

R²·S≡R²S : R² · S ≡ R²S
R²·S≡R²S = transport-refl _
```


## Computing the commutator

The product `SR · SR²` is computed by unfolding through the
`·-s-left` and `·-r-left` compatibility lemmas.

```agda
private
  R∙e₀·SR² : (r∙ e₀) · SR² ≡ r SR²
  R∙e₀·SR² =
    (r∙ e₀) · SR²
      ≡⟨ ap (_· SR²) (sym (r-η e₀)) ⟩
    (r (η e₀)) · SR²
      ≡⟨ ·-r-left (η e₀) SR² ⟩
    r (E · SR²)
      ∎

  r-SR² : r SR² ≡ RSR²
  r-SR² = refl

  s-RSR² : s RSR² ≡ sr∙ cross (r- e₀)
  s-RSR² = refl

SR·SR²-val : SR · SR² ≡ sr∙ cross (r- e₀)
SR·SR²-val =
  SR · SR²
    ≡⟨ ·-s-left (θ (r+ e₀)) SR² ⟩
  s ((θ (r+ e₀)) · SR²)
    ≡⟨ ap s R∙e₀·SR² ⟩
  s (r SR²)
    ∎
```


## Non-commutativity

SR is an eta-form and RS is a theta-form, hence disjoint.

```agda
SR≢RS : SR ≢ RS
SR≢RS = η-is-not-θ _ _

non-commutative : S · R ≢ R · S
non-commutative p = SR≢RS (p ∙ sym R·S≡RS)
```


## Commutator is nontrivial

The commutator `[S,R]` reduces to `sr∙ cross (r- e₀)`, which is
`η (cross (r+ (cross (r- e₀))))`. This is not E = `η e₀`
because the `cross` constructor is distinct from `e₀`.

```agda
private
  cross≢e₀ : (re : R-edge) → cross re ≢ e₀
  cross≢e₀ _ p = subst d p tt where
    d : S-edge → Type 0ℓ
    d e₀        = ⊥
    d e₁        = ⊥
    d (cross _) = ⊤

[S,R]≢E : [ S , R ] ≢ E
[S,R]≢E p = cross≢e₀ _ (η-lc (SR·SR²-val ∙ p))
```


## Depth of the commutator

```agda
depth-[S,R] : depth [ S , R ] ≡ 4
depth-[S,R] = ap depth SR·SR²-val
```
