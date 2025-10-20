```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Trait.Graphical where

open import Prim.Type

record Graphical {u} (A : Type u) : Typeω where
  field
    {l₀ l₁} : Level
    ∣_∣ : A → Type l₀
    _[_,_] : (𝓐 : A) → ∣ 𝓐 ∣ → ∣ 𝓐 ∣ → Type l₁

open Graphical ⦃ ... ⦄ public

```

-- We can also create a public 'open' helper for convenience.
open Displayed ⦃...⦄ public

```

record Reflexive {u} (A : Type u) : Typeω where
  field
    ⦃ Reflexive-Graphical ⦄ : Graphical A
    rfl : (𝓐 : A) {x : ∣ 𝓐 ∣} → 𝓐 [ x , x ]

  syntax rfl 𝓐 {x} = rfl x ∶ 𝓐

open Reflexive ⦃ ... ⦄ public

record Displayable {u v} (A : Type u) (B : A → Type v) : Typeω where
  field
    ⦃ Displayable-Graphical ⦄ : Graphical A
    {l₀ l₁} : Level
    ∣_∣⟨_⟩ : {𝓐 : A} (𝓑 : B 𝓐) → ∣ 𝓐 ∣ → Type l₀
    _⟨_⟩[_,_] : {𝓐 : A} (𝓑 : B 𝓐) {x y : ∣ 𝓐 ∣}
              → 𝓐 [ x , y ] → ∣ 𝓑 ∣⟨ x ⟩ → ∣ 𝓑 ∣⟨ y ⟩ → Type l₁

open Displayable ⦃ ... ⦄ public
