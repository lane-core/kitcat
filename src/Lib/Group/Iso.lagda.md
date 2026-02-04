Group isomorphisms and their basic properties.

Adapted from TypeTopology, Groups.Type (lines 273--351).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Iso where

open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Type using (Level; Type; _⊔_; id; _∘_; ⌞_⌟)
open import Core.Kan using (_∙_)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)

open import Lib.Group.Base
open import Lib.Group.Hom

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


## Isomorphism predicate

A group isomorphism is a homomorphism equipped with a two-sided inverse
that is also a homomorphism.

```agda

record is-iso (G : Grp u) (H : Grp v) (f : ⌞ G ⌟ → ⌞ H ⌟)
  : Type (u ⊔ v) where
  no-eta-equality
  field
    f-is-hom : is-hom G H f
    g        : ⌞ H ⌟ → ⌞ G ⌟
    g-is-hom : is-hom H G g
    unit     : ∀ x → g (f x) ≡ x
    counit   : ∀ y → f (g y) ≡ y

open is-iso public
{-# INLINE is-iso.constructor #-}

```


## Bundled isomorphism type

```agda

_≅_ : Grp u → Grp v → Type (u ⊔ v)
G ≅ H = Σ f ∶ (⌞ G ⌟ → ⌞ H ⌟) , is-iso G H f

```


## Inverses are automatically homomorphisms

If `f` is a homomorphism and `g` is a two-sided inverse of `f`, then
`g` is automatically a homomorphism. This means that when constructing
an isomorphism from a bijective homomorphism, the inverse's
homomorphism property comes for free.

```agda

inverses-are-homs
  : (G : Grp u) (H : Grp v)
  → (f : ⌞ G ⌟ → ⌞ H ⌟) (g : ⌞ H ⌟ → ⌞ G ⌟)
  → is-hom G H f
  → (∀ x → g (f x) ≡ x) → (∀ y → f (g y) ≡ y)
  → is-hom H G g
inverses-are-homs G H f g f-hom η ε x y =
  g (H ._·_ x y)                            ≡˘⟨ ap (λ a → g (H ._·_ a y)) (ε x) ⟩
  g (H ._·_ (f (g x)) y)                    ≡˘⟨ ap (λ b → g (H ._·_ (f (g x)) b)) (ε y) ⟩
  g (H ._·_ (f (g x)) (f (g y)))            ≡˘⟨ ap g (f-hom (g x) (g y)) ⟩
  g (f (G ._·_ (g x) (g y)))                ≡⟨ η (G ._·_ (g x) (g y)) ⟩
  G ._·_ (g x) (g y)                        ∎

```


## Identity isomorphism

```agda

≅-refl : (G : Grp u) → G ≅ G
≅-refl G = id , iso where
  iso : is-iso G G id
  iso .f-is-hom = id-is-hom G
  iso .g        = id
  iso .g-is-hom = id-is-hom G
  iso .unit _   = refl
  iso .counit _ = refl

```


## Inverse isomorphism

```agda

≅-sym : {G : Grp u} {H : Grp v} → G ≅ H → H ≅ G
≅-sym {G = G} {H} (f , iso) = iso .g , iso' where
  iso' : is-iso H G (iso .g)
  iso' .f-is-hom = iso .g-is-hom
  iso' .g        = f
  iso' .g-is-hom = iso .f-is-hom
  iso' .unit     = iso .counit
  iso' .counit   = iso .unit

```


## Composition of isomorphisms

```agda

≅-trans
  : {G : Grp u} {H : Grp v} {K : Grp w}
  → G ≅ H → H ≅ K → G ≅ K
≅-trans {G = G} {H} {K} (f , α) (h , β) = h ∘ f , iso where
  iso : is-iso G K (h ∘ f)
  iso .f-is-hom = ∘-is-hom G H K (α .f-is-hom) (β .f-is-hom)
  iso .g        = α .g ∘ β .g
  iso .g-is-hom = ∘-is-hom K H G (β .g-is-hom) (α .g-is-hom)
  iso .unit x   =
    α .g (β .g (h (f x))) ≡⟨ ap (α .g) (β .unit (f x)) ⟩
    α .g (f x)            ≡⟨ α .unit x ⟩
    x                     ∎
  iso .counit y =
    h (f (α .g (β .g y))) ≡⟨ ap h (α .counit (β .g y)) ⟩
    h (β .g y)            ≡⟨ β .counit y ⟩
    y                     ∎

```
