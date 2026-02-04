Effect: universe-polymorphic type constructors for functor/monad hierarchies.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Quiver where

open import Core.Type
open import Core.Trait.Effect

record Virtual (M : Effect) : Typeω where
  constructor arr
  private module M = Effect M
  field
    {adj} : Level → Level
    {adjₜ} : Level → Level
    ₁ : ∀ {u} {A : Type u} → A → M.₀ A → Type (adj u)
    ₜ : ∀ {u} {A : Type u} → A → A → Type (adjₜ u)
    seqₜ
      : ∀ {u} {A : Type u} {a b c : A}
      → ₜ a b → ₜ b c → ₜ a c
    ₂
      : ∀ {u} {A : Type u} {x y : A} {a b : M.₀ A}
      → ₜ x y → ₁ x a → ₜ a b → ₁ y b → Type (adj u)

-- record Composable {M : Effect} (X : Virtual M) : Typeω where
--   private module M = Effect M
--   private module X = Virtual X
--   field
    -- _<⨾>_
    --   : ∀ {u} {A : Type u} {x y z : A} {a b c : M.₀ A} {i j k : M.₀ (M.₀ A)}
    --   → {f0 : lₜ x y} {f1 : rₜ a b} {f2 : rₜ i j}
    --   → {g0 : lₜ y z} {g1 : rₜ b c} {g2 : rₜ j k}
    --   → {s0 : X.₁ x a} {s1 : X.₁ a i}
    --   → {r0 : X.₁ y b} {r1 : X.₁ b j}
    --   → {t0 : X.₁ y b} {t1 : X.₁ c k}
    --   → ₂ f0 s0 f1 r0
    --   → ₂ {!f1!} s1 f2 r1
    --   → ₂ f0 {!!} f1 {!!}
    --   → ₂ f0 {!!} f1 {!!}
    --   → ₂ f0 {!!} {!f2!} {!!}
