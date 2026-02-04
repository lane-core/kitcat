Effect: universe-polymorphic type constructors for functor/monad hierarchies.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Quiver where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Trait.Effect

record Quiver : Typeω where
  constructor gph
  field
    {adj} : Level → Level → Level
    ob : ∀ u → Type (u ₊)
    ₁ : ∀ {u v} → ob u → ob v → Type (adj u v)

Fun : Quiver
Fun .Quiver.adj = λ u v → u ⊔ v
Fun .Quiver.ob = λ u → Type u
Fun .Quiver.₁ = λ A B → A → B

Pro : Quiver
Pro .Quiver.adj = λ u v → u ⊔ v
Pro .Quiver.ob = λ u → Type u
Pro .Quiver.₁ = λ A B → A × B

record Semicategory (X : Quiver) : Typeω where
  private module X = Quiver X
  field
    seq
      : ∀ {u v w} {a : X.ob u} {b : X.ob v} {c : X.ob w}
      → X.₁ a b → X.₁ b c → X.₁ a c
    @0 assoc
      : ∀ {u v w z} {a : X.ob u} {b : X.ob v} {c : X.ob w} {d : X.ob z}
      → (f : X.₁ a b) (g : X.₁ b c) (h : X.₁ c d)
      → seq (seq f g) h ≡ seq f (seq g h)

record Functor (X Y : Quiver) : Typeω where
  private module X = Quiver X
  private module Y = Quiver Y
  field
    ⦃ Src-semicat ⦄ : Semicategory X
    ⦃ Trg-semicat ⦄ : Semicategory Y
    map : ∀ {u} → X.ob u → Y.ob u
    hmap : ∀ {u v} {a : X.ob u} {b : X.ob v}
         → X.₁ a b → Y.₁ (map a) (map b)
