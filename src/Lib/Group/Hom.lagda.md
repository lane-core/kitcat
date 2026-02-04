Group homomorphisms and their basic properties.

Adapted from TypeTopology, Groups.Type (lines 188--271).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Hom where

open import Core.Transport.Properties using (is-prop→is-set)
open import Core.HLevel using (Π-is-set)
open import Core.Base using (_≡_; refl; sym; ap; is-set)
open import Core.Type using (Level; Type; _⊔_; id; _∘_; ⌞_⌟)
open import Core.Kan using (_∙_)

open import Lib.Group.Base

private variable
  u v w : Level

private
  _≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
          → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ∙ q

  _≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
           → y ≡ x → y ≡ z → x ≡ z
  x ≡˘⟨ p ⟩ q = sym p ∙ q

  _∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
  x ∎ = refl

  infixr 2 _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  3 _∎

```


## Homomorphism predicate

A function between group carriers is a homomorphism when it preserves
multiplication.

```agda

is-hom : (G : Grp u) (H : Grp v) → (⌞ G ⌟ → ⌞ H ⌟) → Type (u ⊔ v)
is-hom G H f = ∀ x y → f (G ._·_ x y) ≡ H ._·_ (f x) (f y)

```


## Single-group lemmas

These lemmas hold in any group and are used in the homomorphism proofs
below.

```agda

module _ {u} (G : Grp u) where
  private
    infixl 7 _*_
    _*_   = G ._·_
    ε     = e G
    _⁻¹   = inv G
    g-asc = Grp.assoc G

```

In a group, the only idempotent element is the unit.

```agda

  idempotent-is-unit : ∀ x → x * x ≡ x → x ≡ ε
  idempotent-is-unit x p =
    x              ≡˘⟨ idl G x ⟩
    ε * x          ≡˘⟨ ap (_* x) (invl G x) ⟩
    (x ⁻¹ * x) * x ≡⟨ g-asc (x ⁻¹) x x ⟩
    x ⁻¹ * (x * x) ≡⟨ ap (x ⁻¹ *_) p ⟩
    x ⁻¹ * x       ≡⟨ invl G x ⟩
    ε              ∎

```

Inverse uniqueness: if `y * x = e` then `y = inv x`.

```agda

  one-left-inv : ∀ x y → y * x ≡ ε → y ≡ x ⁻¹
  one-left-inv x y p =
    y              ≡˘⟨ idr G y ⟩
    y * ε          ≡˘⟨ ap (y *_) (invr G x) ⟩
    y * (x * x ⁻¹) ≡˘⟨ g-asc y x (x ⁻¹) ⟩
    (y * x) * x ⁻¹ ≡⟨ ap (_* x ⁻¹) p ⟩
    ε * x ⁻¹       ≡⟨ idl G (x ⁻¹) ⟩
    x ⁻¹           ∎

```

Inverse uniqueness (right): if `x * y = e` then `y = inv x`.

```agda

  one-right-inv : ∀ x y → x * y ≡ ε → y ≡ x ⁻¹
  one-right-inv x y p =
    y              ≡˘⟨ idl G y ⟩
    ε * y          ≡˘⟨ ap (_* y) (invl G x) ⟩
    (x ⁻¹ * x) * y ≡⟨ g-asc (x ⁻¹) x y ⟩
    x ⁻¹ * (x * y) ≡⟨ ap (x ⁻¹ *_) p ⟩
    x ⁻¹ * ε       ≡⟨ idr G (x ⁻¹) ⟩
    x ⁻¹           ∎

```


## Preservation lemmas

These show that every homomorphism preserves units and inverses.

```agda

module _ {u v} (G : Grp u) (H : Grp v) where
  private
    infixl 7 _*G_ _*H_
    _*G_ = G ._·_
    εG   = e G
    _*H_ = H ._·_
    εH   = e H

```

A homomorphism sends the unit to the unit: from `f(e * e) = f(e) * f(e)`
and `f(e * e) = f(e)`, we get `f(e) * f(e) = f(e)`, so `f(e) = e` by
the idempotent lemma.

```agda

  homs-preserve-unit
    : (f : ⌞ G ⌟ → ⌞ H ⌟)
    → is-hom G H f → f εG ≡ εH
  homs-preserve-unit f μ = idempotent-is-unit H (f εG) idem where
    idem : f εG *H f εG ≡ f εG
    idem =
      f εG *H f εG ≡˘⟨ μ εG εG ⟩
      f (εG *G εG)  ≡⟨ ap f (idl G εG) ⟩
      f εG          ∎

```

A homomorphism sends inverses to inverses: from `f(inv x) * f(x) = e_H`
we conclude `f(inv x) = inv (f x)` by inverse uniqueness.

```agda

  homs-preserve-inv
    : (f : ⌞ G ⌟ → ⌞ H ⌟)
    → is-hom G H f → ∀ x → f (inv G x) ≡ inv H (f x)
  homs-preserve-inv f μ x =
    one-left-inv H (f x) (f (inv G x)) prod-is-unit
    where
    prod-is-unit : f (inv G x) *H f x ≡ εH
    prod-is-unit =
      f (inv G x) *H f x ≡˘⟨ μ (inv G x) x ⟩
      f (inv G x *G x)    ≡⟨ ap f (invl G x) ⟩
      f εG                ≡⟨ homs-preserve-unit f μ ⟩
      εH                  ∎

```


## Closure under identity and composition

```agda

id-is-hom : (G : Grp u) → is-hom G G id
id-is-hom G _ _ = refl

∘-is-hom
  : (G : Grp u) (H : Grp v) (K : Grp w)
  → {f : ⌞ G ⌟ → ⌞ H ⌟} {g : ⌞ H ⌟ → ⌞ K ⌟}
  → is-hom G H f → is-hom H K g → is-hom G K (g ∘ f)
∘-is-hom G H K {f} {g} μf μg x y =
  g (f (G ._·_ x y))              ≡⟨ ap g (μf x y) ⟩
  g (H ._·_ (f x) (f y))          ≡⟨ μg (f x) (f y) ⟩
  K ._·_ (g (f x)) (g (f y))      ∎

```


## is-hom is a set

The homomorphism predicate is valued in the path space of a set, so it
is itself a set.

```agda

is-hom-is-set
  : (G : Grp u) (H : Grp v) (f : ⌞ G ⌟ → ⌞ H ⌟)
  → is-set (is-hom G H f)
is-hom-is-set G H f =
  Π-is-set λ _ → Π-is-set λ _ → is-prop→is-set (has-is-set H _ _)
```
