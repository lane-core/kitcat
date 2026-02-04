Twist automorphism for the modular group PSL(2,Z).

Adapted from TypeTopology, `Groups.ModularGroup.Twist`
(Todd Waugh Ambridge). Defines the twist automorphism that swaps
r and r-squared, proves it is an involution, a group homomorphism,
and characterizes it as generator iteration.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Twist where

open import Core.Transport.Base using (transport-refl)
open import Core.Base using (_≡_; refl; sym; ap; funext)
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


## Twist

The twist automorphism swaps r and r-squared. It is defined by mutual
recursion on S-edges and R-edges.

```agda
twist-η : S-edge → PSL2Z
twist-θ : R-edge → PSL2Z

twist-η e₀         = E
twist-η e₁         = S
twist-η (cross re) = s (twist-θ re)

twist-θ (r+ se) = r² (twist-η se)
twist-θ (r- se) = r (twist-η se)

twist : PSL2Z → PSL2Z
twist (η se) = twist-η se
twist (θ re) = twist-θ re
```


## Compatibility with generators

How twist commutes with the generators s, r, and r-squared.

```agda
twist-s : (x : PSL2Z) → twist (s x) ≡ s (twist x)
twist-s (η e₀)    = refl
twist-s (η e₁)    = refl
twist-s (sr∙ se)  = sym (s² (r (r (twist-η se))))
twist-s (sr²∙ se) = sym (s² (r (twist-η se)))
twist-s (r∙ se)   = refl
twist-s (r²∙ se)  = refl

twist-r : (x : PSL2Z) → twist (r x) ≡ r² (twist x)
twist-r (η e₀)    = refl
twist-r (η e₁)    = refl
twist-r (sr∙ se)  = refl
twist-r (sr²∙ se) = refl
twist-r (r∙ se)   = sym (r³ (r (twist-η se)))
twist-r (r²∙ se)  = sym (r³ (twist-η se))

twist-r² : (x : PSL2Z) → twist (r² x) ≡ r (twist x)
twist-r² (η e₀)          = refl
twist-r² (η e₁)          = refl
twist-r² (sr∙ se)        = refl
twist-r² (sr²∙ se)       = refl
twist-r² (r∙ se)         = sym (r³ (twist-η se))
twist-r² (r²∙ e₀)        = refl
twist-r² (r²∙ e₁)        = refl
twist-r² (r²∙ (cross x)) = refl
```


## Involution

The twist is an involution: applying it twice returns the input.

```agda
twist-involute : (x : PSL2Z) → twist (twist x) ≡ x
twist-involute (η e₀)    = refl
twist-involute (η e₁)    = refl
twist-involute (sr∙ se)  =
  twist (s (r² (twist-η se)))
    ≡⟨ twist-s (r² (twist-η se)) ⟩
  s (twist (r² (twist-η se)))
    ≡⟨ ap s (twist-r² (twist-η se)) ⟩
  s (r (twist (twist-η se)))
    ≡⟨ ap (s ∘ r) (twist-involute (η se)) ⟩
  s (r (η se))
    ≡⟨ sr-η se ⟩
  sr∙ se
    ∎
twist-involute (sr²∙ se) =
  twist (s (r (twist-η se)))
    ≡⟨ twist-s (r (twist-η se)) ⟩
  s (twist (r (twist-η se)))
    ≡⟨ ap s (twist-r (twist-η se)) ⟩
  s (r² (twist (twist-η se)))
    ≡⟨ ap (s ∘ r²) (twist-involute (η se)) ⟩
  s (r² (η se))
    ≡⟨ sr²-η se ⟩
  sr²∙ se
    ∎
twist-involute (r∙ se) =
  twist (r² (twist-η se))
    ≡⟨ twist-r² (twist-η se) ⟩
  r (twist (twist-η se))
    ≡⟨ ap r (twist-involute (η se)) ⟩
  r (η se)
    ≡⟨ r-η se ⟩
  r∙ se
    ∎
twist-involute (r²∙ se)  =
  twist (r (twist-η se))
    ≡⟨ twist-r (twist-η se) ⟩
  r² (twist (twist-η se))
    ≡⟨ ap r² (twist-involute (η se)) ⟩
  r² (η se)
    ≡⟨ r²-η se ⟩
  r²∙ se
    ∎
```


## Homomorphism

The twist preserves multiplication.

```agda
twist-product
  : (x y : PSL2Z) → twist (x · y) ≡ twist x · twist y
twist-product = PSL2Z-ind base-E base-S ind-s ind-r
  where
    base-E : (y : PSL2Z)
      → twist (E · y) ≡ twist E · twist y
    base-E y = refl

    base-S : (y : PSL2Z)
      → twist (S · y) ≡ twist S · twist y
    base-S y = twist-s y

    ind-s
      : (re : R-edge)
      → ((y : PSL2Z)
        → twist ((θ re) · y) ≡ twist (θ re) · twist y)
      → (y : PSL2Z)
        → twist ((s∙ re) · y) ≡ twist (s∙ re) · twist y
    ind-s re ih y =
      twist ((s∙ re) · y)
        ≡⟨ ap twist (·-s-left (θ re) y) ⟩
      twist (s ((θ re) · y))
        ≡⟨ twist-s ((θ re) · y) ⟩
      s (twist ((θ re) · y))
        ≡⟨ ap s (ih y) ⟩
      s (twist (θ re) · twist y)
        ≡⟨ sym (·-s-left (twist (θ re)) (twist y)) ⟩
      (s (twist (θ re))) · twist y
        ≡⟨ ap (_· twist y) (sym (twist-s (θ re))) ⟩
      twist (s∙ re) · twist y
        ∎

    ind-r
      : (d : R-sgn) (se : S-edge)
      → ((y : PSL2Z)
        → twist ((η se) · y) ≡ twist (η se) · twist y)
      → (y : PSL2Z)
        → twist ((ρ d se) · y) ≡ twist (ρ d se) · twist y
    ind-r cw se ih y =
      twist ((r∙ se) · y)
        ≡⟨ ap (twist ∘ (_· y)) (sym (r-η se)) ⟩
      twist ((r (η se)) · y)
        ≡⟨ ap twist (·-r-left (η se) y) ⟩
      twist (r ((η se) · y))
        ≡⟨ twist-r ((η se) · y) ⟩
      r² (twist ((η se) · y))
        ≡⟨ ap r² (ih y) ⟩
      r² (twist (η se) · twist y)
        ≡⟨ sym (·-r²-left (twist (η se)) (twist y)) ⟩
      (r² (twist (η se))) · twist y
        ≡⟨ ap (_· twist y) (sym (twist-r (η se))) ⟩
      twist (r (η se)) · twist y
        ≡⟨ ap (_· twist y) (ap twist (r-η se)) ⟩
      twist (r∙ se) · twist y
        ∎
    ind-r ccw se ih y =
      twist ((r²∙ se) · y)
        ≡⟨ ap (twist ∘ (_· y)) (sym (r²-η se)) ⟩
      twist ((r² (η se)) · y)
        ≡⟨ ap twist (·-r²-left (η se) y) ⟩
      twist (r² ((η se) · y))
        ≡⟨ twist-r² ((η se) · y) ⟩
      r (twist ((η se) · y))
        ≡⟨ ap r (ih y) ⟩
      r (twist (η se) · twist y)
        ≡⟨ sym (·-r-left (twist (η se)) (twist y)) ⟩
      (r (twist (η se))) · twist y
        ≡⟨ ap (_· twist y) (sym (twist-r² (η se))) ⟩
      twist (r² (η se)) · twist y
        ≡⟨ ap (_· twist y) (ap twist (r²-η se)) ⟩
      twist (r²∙ se) · twist y
        ∎
```


## Generator iteration characterizations

The twist is the canonical PSL2Z-gen-iter with identity, s, and
r-squared.

```agda
twist-gen-iter : twist ≡ PSL2Z-gen-iter E s r²
twist-gen-iter = funext lemma where
  lemma : (x : PSL2Z) → twist x ≡ PSL2Z-gen-iter E s r² x
  lemma = PSL2Z-initiality twist refl twist-s twist-r
```

The twist is also the canonical PSL2Z-iter with identity, S, s,
r-squared, and r. We prove this by composing `twist-gen-iter` with
a pointwise equality between `PSL2Z-gen-iter E s r²` and
`PSL2Z-iter E S s r² r`, established by direct induction on PSL2Z.

```agda
private
  gi : PSL2Z → PSL2Z
  gi = PSL2Z-gen-iter E s r²

  it : PSL2Z → PSL2Z
  it = PSL2Z-iter E S s r² r

  gi≡it : (x : PSL2Z) → gi x ≡ it x
  gi≡it = PSL2Z-ind base-E base-S ind-s ind-r where
    base-E : gi E ≡ it E
    base-E = refl

    base-S : gi S ≡ it S
    base-S = refl

    ind-s
      : (re : R-edge) → gi (θ re) ≡ it (θ re)
      → gi (s∙ re) ≡ it (s∙ re)
    ind-s re p = ap s p

    ind-r
      : (d : R-sgn) (se : S-edge)
      → gi (η se) ≡ it (η se)
      → gi (ρ d se) ≡ it (ρ d se)
    ind-r cw se p =
      transport-refl (r² (gi (η se))) ∙ ap r² p
    ind-r ccw se p =
      ap r² (transport-refl (r² (gi (η se))))
      ∙ r³ (r (gi (η se)))
      ∙ ap r p

twist-iter : twist ≡ PSL2Z-iter E S s r² r
twist-iter = twist-gen-iter ∙ funext gi≡it
```
