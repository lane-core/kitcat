Universal property of the modular group PSL(2,Z).

PSL(2,Z) is the initial object among groups
with distinguished elements s and r satisfying s^2 = 1 and r^3 = 1.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.UniversalProperty where

open import Core.Base using (_≡_; refl; sym; ap; is-contr; Contr; funext)
open import Core.Type using (Level; Type; 0ℓ; _∘_)
open import Core.Kan using (_∙_)
open import Core.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Core.Trait.Trunc using (Π-is-prop; Σ-prop-path)
open import Core.Transport.J using (subst)
open import Core.Transport.Base using (transport-refl)

open import Lib.Group.Modular.Type
open import Lib.Group.Modular.Base
open import Lib.Group.Modular.Properties
open import Lib.Group.Modular.Induction
open import Lib.Group.Modular.Multiplication

private variable
  u : Level

private
  _≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
          → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ∙ q

  _∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
  x ∎ = refl

  infixr 2 _≡⟨_⟩_
  infix  3 _∎
```


## PSL2Z-algebra

A PSL2Z-algebra packages a type with an element and two
endomorphisms satisfying the modular group relations.

```agda
PSL2Z-algebra : Type u → Type u
PSL2Z-algebra X =
  Σ λ (sf : X → X) → Σ λ (rf : X → X) →
    ((x : X) → sf (sf x) ≡ x) × ((x : X) → rf (rf (rf x)) ≡ x)
```


## The canonical homomorphism

Given a PSL2Z-algebra on X with base point e, the canonical map
from PSL2Z to X is the generator iteration.

```agda
hmap
  : {X : Type u}
  → X → (sf rf : X → X)
  → PSL2Z → X
hmap e sf rf = PSL2Z-gen-iter e sf rf
```


## hmap preserves E

```agda
hmap-E
  : {X : Type u}
  → (e : X) (sf rf : X → X)
  → hmap e sf rf E ≡ e
hmap-E e sf rf = refl
```


## hmap commutes with s

The canonical map commutes with s, given the involution law on sf.

Under `--erased-cubical`, `PSL2Z-gen-iter` unfolds through
`PSL2Z-gen-ind`, and at the S case we get `h (s S) = h E = e` while
`sf (h S) = sf (sf e)`, requiring the involution law `sf (sf e) = e`.
Similarly for the s-cross case.

```agda
hmap-s
  : {X : Type u}
  → (e : X) (sf rf : X → X)
  → ((x : X) → sf (sf x) ≡ x)
  → (x : PSL2Z) → hmap e sf rf (s x) ≡ sf (hmap e sf rf x)
hmap-s e sf rf sf² = PSL2Z-ind base-E base-S ind-s ind-r where
  h = hmap e sf rf

  base-E : h (s E) ≡ sf (h E)
  base-E = refl

  base-S : h (s S) ≡ sf (h S)
  base-S = sym (sf² e)

  ind-s
    : (re : R-edge) → h (s (θ re)) ≡ sf (h (θ re))
    → h (s (s∙ re)) ≡ sf (h (s∙ re))
  ind-s re p = sym (sf² (h (θ re)))

  ind-r
    : (d : R-sgn) (se : S-edge)
    → h (s (η se)) ≡ sf (h (η se))
    → h (s (θ step d se)) ≡ sf (h (θ step d se))
  ind-r d se _ = refl
```


## hmap commutes with r

The canonical map commutes with r, given the order-3 law on rf.

Under `--erased-cubical`, `subst (λ _ → X) refl` does not reduce,
so the `r∙` cases require `transport-refl`. The `r²∙`/ccw cases
require the order-3 law because the iteration at `r²∙ se` is
`rf (subst ... (rf (h (η se))))`, and `h (r (r²∙ se)) = h (η se)`,
so we need `rf (rf (rf x)) ≡ x`.

```agda
hmap-r
  : {X : Type u}
  → (e : X) (sf rf : X → X)
  → ((x : X) → rf (rf (rf x)) ≡ x)
  → (x : PSL2Z) → hmap e sf rf (r x) ≡ rf (hmap e sf rf x)
hmap-r e sf rf rf³ = PSL2Z-ind base-E base-S ind-s ind-r where
  h = hmap e sf rf

  base-E : h (r E) ≡ rf (h E)
  base-E = transport-refl _

  base-S : h (r S) ≡ rf (h S)
  base-S = transport-refl _

  ind-s
    : (re : R-edge) → h (r (θ re)) ≡ rf (h (θ re))
    → h (r (s∙ re)) ≡ rf (h (s∙ re))
  ind-s re _ = transport-refl _

  ind-r
    : (d : R-sgn) (se : S-edge)
    → h (r (η se)) ≡ rf (h (η se))
    → h (r (θ step d se)) ≡ rf (h (θ step d se))
  ind-r cw  e₀         _ = refl
  ind-r cw  e₁         _ = refl
  ind-r cw  (cross re) _ = refl
  ind-r ccw se         _ =
    let a = h (η se)
    in sym (ap rf (ap rf (transport-refl (rf a))) ∙ rf³ a)
```


## hmap preserves multiplication

For any y, the function `λ x → hmap (x · y)` agrees with
`PSL2Z-gen-iter (hmap y) sf rf`. We use PSL2Z-eta uniqueness,
using the preceding commutation lemmas.

```agda
hmap-mul
  : {X : Type u}
  → (e : X) (sf rf : X → X)
  → (sf² : (x : X) → sf (sf x) ≡ x)
  → (rf³ : (x : X) → rf (rf (rf x)) ≡ x)
  → (x y : PSL2Z)
  → hmap e sf rf (x · y)
    ≡ PSL2Z-gen-iter (hmap e sf rf y) sf rf x
hmap-mul e sf rf sf² rf³ x y = PSL2Z-η sf rf f g base f-s g-s f-r g-r x
  where
    h = hmap e sf rf

    f : PSL2Z → _
    f x = h (x · y)

    g : PSL2Z → _
    g x = PSL2Z-gen-iter (h y) sf rf x

    base : f E ≡ g E
    base = refl

    f-s : (x : PSL2Z) → f (s x) ≡ sf (f x)
    f-s x =
      h ((s x) · y)  ≡⟨ ap h (·-s-left x y) ⟩
      h (s (x · y))  ≡⟨ hmap-s e sf rf sf² (x · y) ⟩
      sf (h (x · y)) ∎

    g-s : (x : PSL2Z) → g (s x) ≡ sf (g x)
    g-s x = hmap-s (h y) sf rf sf² x

    f-r : (x : PSL2Z) → f (r x) ≡ rf (f x)
    f-r x =
      h ((r x) · y)  ≡⟨ ap h (·-r-left x y) ⟩
      h (r (x · y))  ≡⟨ hmap-r e sf rf rf³ (x · y) ⟩
      rf (h (x · y)) ∎

    g-r : (x : PSL2Z) → g (r x) ≡ rf (g x)
    g-r x = hmap-r (h y) sf rf rf³ x
```


## Uniqueness

Any function `f : PSL2Z → X` that preserves E, commutes with s,
and commutes with r must equal hmap pointwise. This uses PSL2Z-eta
uniqueness.

```agda
hmap-unique
  : {X : Type u}
  → (e : X) (sf rf : X → X)
  → (sf² : (x : X) → sf (sf x) ≡ x)
  → (rf³ : (x : X) → rf (rf (rf x)) ≡ x)
  → (f : PSL2Z → X)
  → f E ≡ e
  → ((x : PSL2Z) → f (s x) ≡ sf (f x))
  → ((x : PSL2Z) → f (r x) ≡ rf (f x))
  → (x : PSL2Z) → f x ≡ hmap e sf rf x
hmap-unique e sf rf sf² rf³ f f-E f-s f-r =
  PSL2Z-η sf rf f (hmap e sf rf) f-E
    f-s (hmap-s e sf rf sf²)
    f-r (hmap-r e sf rf rf³)
```


## Universal property

The type of homomorphisms from PSL(2,Z) to a PSL2Z-algebra
(X, e, sf, rf) satisfying s^2 = id and r^3 = id is contractible.

A homomorphism is a function preserving E, commuting with s, and
commuting with r.

```agda
PSL2Z-Hom
  : {X : Type u}
  → X → (sf rf : X → X) → Type u
PSL2Z-Hom {X = X} e sf rf =
  Σ λ (f : PSL2Z → X) →
      (f E ≡ e)
    × ((x : PSL2Z) → f (s x) ≡ sf (f x))
    × ((x : PSL2Z) → f (r x) ≡ rf (f x))
```

When X is a set, the type of such homomorphisms is contractible.

```agda
universal
  : {X : Type u}
  → (X-set : (a b : X) → (p q : a ≡ b) → p ≡ q)
  → (e : X) (sf rf : X → X)
  → (sf² : (x : X) → sf (sf x) ≡ x)
  → (rf³ : (x : X) → rf (rf (rf x)) ≡ x)
  → is-contr (PSL2Z-Hom e sf rf)
universal {X = X} X-set e sf rf sf² rf³ .is-contr.center =
  hmap e sf rf , refl , hmap-s e sf rf sf² , hmap-r e sf rf rf³
universal {X = X} X-set e sf rf sf² rf³ .is-contr.paths
  (f , f-E , f-s , f-r) =
    Σ-prop-path (λ a → hom-prop a)
      (funext (λ x →
        sym (hmap-unique e sf rf sf² rf³ f f-E f-s f-r x)))
    where
      ×-is-prop
        : ∀ {v w} {A : Type v} {B : Type w}
        → ((x y : A) → x ≡ y)
        → ((x y : B) → x ≡ y)
        → (x y : A × B) → x ≡ y
      ×-is-prop pa pb (a₁ , b₁) (a₂ , b₂) i =
        pa a₁ a₂ i , pb b₁ b₂ i

      hom-prop
        : (a : PSL2Z → X)
        → (p q : (a E ≡ e)
                 × ((x : PSL2Z) → a (s x) ≡ sf (a x))
                 × ((x : PSL2Z) → a (r x) ≡ rf (a x)))
        → p ≡ q
      hom-prop a = ×-is-prop
        (X-set (a E) e)
        (×-is-prop
          (Π-is-prop (λ x → X-set (a (s x)) (sf (a x))))
          (Π-is-prop (λ x → X-set (a (r x)) (rf (a x)))))
```
