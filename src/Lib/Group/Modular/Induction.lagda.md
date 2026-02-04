Induction principles for the modular group PSL(2,Z).

Adapted from TypeTopology, `Groups.ModularGroup.Induction`
(Todd Waugh Ambridge). Mutual induction on S-edges and R-edges,
plus general induction and recursion on PSL2Z, an initiality theorem,
and an eta-expansion uniqueness principle.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Induction where

open import Core.Type using (Level; Type; 0ℓ)
open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Transport.Base using (transport-refl)

open import Lib.Group.Modular.Type
open import Lib.Group.Modular.Base
open import Lib.Group.Modular.Properties

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


## Mutual edge induction

Induction on S-edges and R-edges simultaneously, reflecting the mutual
structure of the Cayley graph.

```agda
S-edge-ind
  : {P : S-edge → Type u}
  → {Q : R-edge → Type u}
  → P e₀
  → P e₁
  → ((re : R-edge) → Q re → P (cross re))
  → ((d : R-sgn) (se : S-edge) → P se → Q (step d se))
  → (se : S-edge) → P se

R-edge-ind
  : {P : S-edge → Type u}
  → {Q : R-edge → Type u}
  → P e₀
  → P e₁
  → ((re : R-edge) → Q re → P (cross re))
  → ((d : R-sgn) (se : S-edge) → P se → Q (step d se))
  → (re : R-edge) → Q re

S-edge-ind p₀ p₁ c t e₀         = p₀
S-edge-ind p₀ p₁ c t e₁         = p₁
S-edge-ind p₀ p₁ c t (cross re) =
  c re (R-edge-ind p₀ p₁ c t re)

R-edge-ind p₀ p₁ c t (step d se) =
  t d se (S-edge-ind p₀ p₁ c t se)
```


## PSL2Z induction

Dependent elimination for PSL2Z, reducing to the mutual edge induction.

```agda
PSL2Z-ind
  : {P : PSL2Z → Type u}
  → P E
  → P S
  → ((re : R-edge) → P (θ re) → P (s∙ re))
  → (∀ d se → P (η se) → P (ρ d se))
  → (x : PSL2Z) → P x
PSL2Z-ind {u} {P} p₀ p₁ c t (η se) =
  S-edge-ind {u}
    {λ se → P (η se)} {λ re → P (θ re)}
    p₀ p₁ c t se
PSL2Z-ind {u} {P} p₀ p₁ c t (θ re) =
  R-edge-ind {u}
    {λ se → P (η se)} {λ re → P (θ re)}
    p₀ p₁ c t re
```


## PSL2Z recursion

Non-dependent elimination, a special case of induction.

```agda
PSL2Z-rec
  : {X : Type u}
  → X → X
  → ((re : R-edge) → X → X)
  → ((d : R-sgn) (se : S-edge) → X → X)
  → PSL2Z → X
PSL2Z-rec {u} {X} x₀ x₁ c t =
  PSL2Z-ind {u} {λ _ → X} x₀ x₁ c t
```


## PSL2Z iteration

Recursion where the step functions ignore the edge data.

```agda
PSL2Z-iter
  : {X : Type u}
  → X → X → (X → X) → (X → X) → (X → X)
  → PSL2Z → X
PSL2Z-iter e s c f-cw f-ccw =
  PSL2Z-rec e s
    (λ _ → c)
    (λ { cw _ → f-cw ; ccw _ → f-ccw })
```


## Generator induction

Induction in terms of the abstract generators s and r, using subst to
handle the definitional mismatch at R-edges.

```agda
PSL2Z-gen-ind
  : {P : PSL2Z → Type u}
  → P E
  → ((x : PSL2Z) → P x → P (s x))
  → ((x : PSL2Z) → P x → P (r x))
  → (x : PSL2Z) → P x
PSL2Z-gen-ind {u} {P} p₀ ps pr =
  PSL2Z-ind p₀ (ps E p₀) c t where
    t : (d : R-sgn) (se : S-edge)
      → P (η se) → P (θ step d se)
    t cw  se p =
      subst P (r-η se) (pr (η se) p)
    t ccw se p =
      pr (r∙ se) (subst P (r-η se) (pr (η se) p))

    c : (re : R-edge) → P (θ re) → P (s∙ re)
    c re p = ps (θ re) p
```


## Generator iteration

Non-dependent generator induction.

```agda
PSL2Z-gen-iter
  : {X : Type u} → X → (X → X) → (X → X) → PSL2Z → X
PSL2Z-gen-iter x₀ fs fr =
  PSL2Z-gen-ind x₀ (λ _ → fs) (λ _ → fr)
```


## Eta-expansion uniqueness

Two functions agreeing on E, commuting with s and r, agree everywhere.

```agda
PSL2Z-η
  : {X : Type u} (fs fr : X → X)
  → (f g : PSL2Z → X)
  → f E ≡ g E
  → ((x : PSL2Z) → f (s x) ≡ fs (f x))
  → ((x : PSL2Z) → g (s x) ≡ fs (g x))
  → ((x : PSL2Z) → f (r x) ≡ fr (f x))
  → ((x : PSL2Z) → g (r x) ≡ fr (g x))
  → (x : PSL2Z) → f x ≡ g x
PSL2Z-η fs fr f g base f-s g-s f-r g-r =
  PSL2Z-gen-ind base ind-s ind-r where
    ind-s : (x : PSL2Z) → f x ≡ g x → f (s x) ≡ g (s x)
    ind-s x p =
      f (s x)  ≡⟨ f-s x ⟩
      fs (f x) ≡⟨ ap fs p ⟩
      fs (g x) ≡⟨ sym (g-s x) ⟩
      g (s x)  ∎

    ind-r : (x : PSL2Z) → f x ≡ g x → f (r x) ≡ g (r x)
    ind-r x p =
      f (r x)  ≡⟨ f-r x ⟩
      fr (f x) ≡⟨ ap fr p ⟩
      fr (g x) ≡⟨ sym (g-r x) ⟩
      g (r x)  ∎
```


## Initiality

The canonical iteration with generators s and r-squared is initial
among PSL2Z endomorphisms preserving the generator equations.

```agda
PSL2Z-gen-iter-E
  : {X : Type u} (x₀ : X) (fs fr : X → X)
  → PSL2Z-gen-iter x₀ fs fr E ≡ x₀
PSL2Z-gen-iter-E x₀ fs fr = refl

private
  iter : PSL2Z → PSL2Z
  iter = PSL2Z-gen-iter E s r²

PSL2Z-gen-iter-s
  : (x : PSL2Z) → iter (s x) ≡ s (iter x)
PSL2Z-gen-iter-s = PSL2Z-ind base-E base-S ind-s ind-r
  where
    base-E : iter (s E) ≡ s (iter E)
    base-E = refl

    base-S : iter (s S) ≡ s (iter S)
    base-S = refl

    ind-s
      : (re : R-edge) → iter (s (θ re)) ≡ s (iter (θ re))
      → iter (s (s∙ re)) ≡ s (iter (s∙ re))
    ind-s re p =
      iter (s (s∙ re))    ≡⟨ refl ⟩
      iter (θ re)         ≡⟨ sym (s² (iter (θ re))) ⟩
      s (s (iter (θ re))) ≡⟨ refl ⟩
      s (iter (s∙ re))    ∎

    ind-r
      : (d : R-sgn) (se : S-edge)
      → iter (s (η se)) ≡ s (iter (η se))
      → iter (s (θ step d se)) ≡ s (iter (θ step d se))
    ind-r d se p = refl

PSL2Z-gen-iter-r
  : (x : PSL2Z) → iter (r x) ≡ r² (iter x)
PSL2Z-gen-iter-r = PSL2Z-ind base-E base-S ind-s ind-r
  where
    base-E : iter (r E) ≡ r² (iter E)
    base-E = transport-refl _

    base-S : iter (r S) ≡ r² (iter S)
    base-S = transport-refl _

    ind-s
      : (re : R-edge) → iter (r (θ re)) ≡ r² (iter (θ re))
      → iter (r (s∙ re)) ≡ r² (iter (s∙ re))
    ind-s re p = transport-refl _

    ind-r
      : (d : R-sgn) (se : S-edge)
      → iter (r (η se)) ≡ r² (iter (η se))
      → iter (r (θ step d se)) ≡ r² (iter (θ step d se))
    ind-r cw  e₀         p = refl
    ind-r cw  e₁         p = refl
    ind-r cw  (cross re) p = refl
    ind-r ccw e₀         p = refl
    ind-r ccw e₁         p = refl
    ind-r ccw (cross re) p =
      let y = s (iter (θ re))
      in sym (r³ (r (r (r y))) ∙ r³ y)
         ∙ ap (λ z → r (r (r (r z))))
              (sym (transport-refl (r (r y))))

PSL2Z-initiality
  : (f : PSL2Z → PSL2Z)
  → f E ≡ E
  → ((x : PSL2Z) → f (s x) ≡ s (f x))
  → ((x : PSL2Z) → f (r x) ≡ r² (f x))
  → (x : PSL2Z) → f x ≡ iter x
PSL2Z-initiality f f-E f-s f-r =
  PSL2Z-η s r² f iter f-E
    f-s PSL2Z-gen-iter-s
    f-r PSL2Z-gen-iter-r
```
