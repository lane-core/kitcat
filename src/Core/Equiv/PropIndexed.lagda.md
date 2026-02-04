Simplification lemmas for Pi and Sigma over propositions.

Credit: TypeTopology, UF.PropIndexedPiSigma (Escardo)

When the index type is a proposition and we have a witness, the
dependent product (resp. dependent sum) over it is equivalent to
the fiber at that witness.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Equiv.PropIndexed where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Transport
open import Core.Equiv
open import Core.Kan

private variable
  u v : Level

```

## Pi over a proposition

When `X` is a proposition and `a : X`, the dependent function type
`(x : X) → Y x` is equivalent to `Y a`. The forward map evaluates
at `a`; the inverse extends using the proposition's path.

```agda

module _ {X : Type u} {Y : X → Type v}
  (prop : is-prop X) (a : X)
  where

  Π-prop-index : ((x : X) → Y x) ≃ Y a
  Π-prop-index = iso→equiv fwd inv sec retr where
    fwd : ((x : X) → Y x) → Y a
    fwd f = f a

    inv : Y a → (x : X) → Y x
    inv y x = subst Y (prop a x) y

    sec : (f : (x : X) → Y x) → inv (fwd f) ≡ f
    sec f = funext λ x →
      Path-over.from-pathp (ap f (prop a x))

    retr : (y : Y a) → fwd (inv y) ≡ y
    retr y =
      ap (λ p → subst Y p y) (is-prop→is-set prop a a (prop a a) refl)
      ∙ transport-refl y

```

## Sigma over a proposition

When `X` is a proposition and `a : X`, the dependent sum
`Σ X Y` is equivalent to `Y a`. The forward map transports the
fiber to `a`; the inverse pairs with `a`.

```agda

  Σ-prop-index : (Σ x ∶ X , Y x) ≃ Y a
  Σ-prop-index = iso→equiv fwd inv sec retr where
    fwd : (Σ x ∶ X , Y x) → Y a
    fwd (x , y) = subst Y (sym (prop a x)) y

    inv : Y a → Σ x ∶ X , Y x
    inv y = a , y

    sec : (p : Σ x ∶ X , Y x) → inv (fwd p) ≡ p
    sec (x , y) i = prop a x i , q i where
      q : PathP (λ i → Y (prop a x i))
            (subst Y (sym (prop a x)) y) y
      q = Path-over.to-pathp
            (transport⁻-transport (ap Y (prop a x)) y)

    retr : (y : Y a) → fwd (inv y) ≡ y
    retr y =
      ap (λ p → subst Y (sym p) y)
        (is-prop→is-set prop a a (prop a a) refl)
      ∙ transport-refl y

```
