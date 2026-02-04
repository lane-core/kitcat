Depth filtration of the modular group PSL(2,Z).

Enumerates elements by depth and proves that the abelianization
map separates elements at low depth. In particular, the only
element with trivial abelianization image at depth at most 2 is
the identity.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Depth.Filtration where

open import Core.Base using (_≡_; refl; sym; ap)
open import Core.Type using (Type; 0ℓ; ⊤; tt)
open import Core.Kan using (_∙_)
open import Core.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Core.Data.Sum using (_⊎_; inl; inr)
open import Core.Data.Bool using (Bool; true; false)
open import Core.Data.Empty using (⊥; ex-falso)
open import Core.Data.Nat.Type using (Nat; Z)
  renaming (S to suc)
open import Core.Path using (_≢_)
open import Core.Transport.J using (subst)

open import Lib.Group.Modular.CommutatorSubgroup
open import Lib.Group.Modular.Abelianization
open import Lib.Group.Modular.Properties
open import Lib.Group.Modular.Type
open import Lib.Group.Modular.Depth
```


## Abelianization checks

Computational verification that the ab map takes known values on
elements of depth at most 2.

```agda
private
  ab-E   : ab E   ≡ (false , 𝟬); ab-E   = refl
  ab-S   : ab S   ≡ (true  , 𝟬); ab-S   = refl
  ab-R   : ab R   ≡ (false , 𝟭); ab-R   = refl
  ab-R²  : ab R²  ≡ (false , 𝟮); ab-R²  = refl
  ab-SR  : ab SR  ≡ (true  , 𝟭); ab-SR  = refl
  ab-SR² : ab SR² ≡ (true  , 𝟮); ab-SR² = refl
  ab-RS  : ab RS  ≡ (true  , 𝟭); ab-RS  = refl
  ab-R²S : ab R²S ≡ (true  , 𝟮); ab-R²S = refl
```


## Discrimination helpers

```agda
private
  true≢false : true ≢ false
  true≢false p = subst d p tt where
    d : Bool → Type 0ℓ
    d false = ⊥
    d true  = ⊤

  𝟭≢𝟬 : 𝟭 ≢ 𝟬
  𝟭≢𝟬 p = subst d p tt where
    d : 𝟛 → Type 0ℓ
    d 𝟬 = ⊥
    d 𝟭 = ⊤
    d 𝟮 = ⊥

  𝟮≢𝟬 : 𝟮 ≢ 𝟬
  𝟮≢𝟬 p = subst d p tt where
    d : 𝟛 → Type 0ℓ
    d 𝟬 = ⊥
    d 𝟭 = ⊥
    d 𝟮 = ⊤
```


## Bounded-depth predicate

We define a predicate on PSL2Z that captures "depth at most n"
by mutual recursion on the edge types. This avoids issues with
the ordering relation under `--erased-cubical`.

```agda
data BoundedS : Nat → S-edge → Type 0ℓ
data BoundedR : Nat → R-edge → Type 0ℓ

data BoundedS where
  b-e₀    : ∀ {n} → BoundedS n e₀
  b-e₁    : ∀ {n} → BoundedS (suc n) e₁
  b-cross : ∀ {n re}
    → BoundedR n re → BoundedS (suc n) (cross re)

data BoundedR where
  b-step : ∀ {n d se}
    → BoundedS n se → BoundedR (suc n) (step d se)

Bounded : Nat → PSL2Z → Type 0ℓ
Bounded n (η se) = BoundedS n se
Bounded n (θ re) = BoundedR n re
```


## Bounded witnesses for named elements

```agda
private
  b-E   : Bounded 0 E;   b-E   = b-e₀
  b-S   : Bounded 1 S;   b-S   = b-e₁
  b-R   : Bounded 1 R;   b-R   = b-step b-e₀
  b-R²  : Bounded 1 R²;  b-R²  = b-step b-e₀
  b-SR  : Bounded 2 SR;  b-SR  = b-cross (b-step b-e₀)
  b-SR² : Bounded 2 SR²; b-SR² = b-cross (b-step b-e₀)
  b-RS  : Bounded 2 RS;  b-RS  = b-step b-e₁
  b-R²S : Bounded 2 R²S; b-R²S = b-step b-e₁
```


## Main theorem

If x has bounded depth at most 2 and ab x = 0^A, then x = E.

The proof works by pattern matching on the BoundedS/BoundedR
witness, which constrains the element to one of the 8 known
forms. Each non-E case has nontrivial abelianization.

```agda
private
  ker-θ-inner : (d : R-sgn) (se : S-edge)
    → BoundedS 0 se
    → ab-θ (step d se) ≡ 0ᴬ → ⊥
  ker-θ-inner cw  e₀ _ q = 𝟭≢𝟬 (ap snd q)
  ker-θ-inner ccw e₀ _ q = 𝟮≢𝟬 (ap snd q)

  ker-η : ∀ {se}
    → BoundedS 2 se → ab-η se ≡ 0ᴬ → se ≡ e₀
  ker-η b-e₀ _ = refl
  ker-η b-e₁ q = ex-falso (true≢false (ap fst q))
  ker-η {cross (step cw e₀)} (b-cross (b-step b-e₀)) q =
    ex-falso (true≢false (ap fst q))
  ker-η {cross (step ccw e₀)} (b-cross (b-step b-e₀)) q =
    ex-falso (true≢false (ap fst q))

  ker-θ : ∀ {re}
    → BoundedR 2 re → ab-θ re ≡ 0ᴬ → ⊥
  ker-θ {step d e₀} (b-step b-e₀) q =
    ker-θ-inner d e₀ b-e₀ q
  ker-θ {step cw  e₁} (b-step b-e₁) q =
    true≢false (ap fst q)
  ker-θ {step ccw e₁} (b-step b-e₁) q =
    true≢false (ap fst q)

ker-ab-bounded
  : (x : PSL2Z) → Bounded 2 x → ab x ≡ 0ᴬ → x ≡ E
ker-ab-bounded (η se) b q = ap η_ (ker-η b q)
ker-ab-bounded (θ re) b q = ex-falso (ker-θ b q)
```


## Corollary

No nontrivial commutator exists at bounded depth 2. Since
commutators lie in ker(ab), any commutator with a bounded-depth
witness must be E.

```agda
commutator-bounded
  : (x y : PSL2Z)
  → Bounded 2 [ x , y ]
  → [ x , y ] ≡ E
commutator-bounded x y b =
  ker-ab-bounded [ x , y ] b (commutator-in-kernel x y)
```
