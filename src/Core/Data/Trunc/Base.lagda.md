Basic operations on propositional truncation.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Trunc.Base where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Trunc.Type
open import Core.Trait.Trunc using (Π-is-prop)

private variable
  ℓ ℓ' : Level
  A B C P : Type ℓ

```

## Basic properties

```agda

prop : is-prop ∥ A ∥
prop = squash

```


## Elimination principles

```agda

rec : is-prop P → (A → P) → ∥ A ∥ → P
rec P-prop f ∣ a ∣ = f a
rec P-prop f (squash x y i) =
  P-prop (rec P-prop f x) (rec P-prop f y) i

elim : {P : ∥ A ∥ → Type ℓ'}
     → ((x : ∥ A ∥) → is-prop (P x))
     → ((a : A) → P ∣ a ∣)
     → (x : ∥ A ∥) → P x
elim P-prop f ∣ a ∣ = f a
elim P-prop f (squash x y i) =
  is-prop→PathP (λ i → P-prop (squash x y i))
                (elim P-prop f x)
                (elim P-prop f y) i

```


## Functorial action

```agda

map : (A → B) → ∥ A ∥ → ∥ B ∥
map f = rec squash (λ a → ∣ f a ∣)

map₂ : (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
map₂ f = rec (Π-is-prop λ _ → squash) (λ a → map (f a))

```


## Extraction

```agda

out : is-prop A → ∥ A ∥ → A
out A-prop = rec A-prop (λ a → a)

unit : A → ∥ A ∥
unit = ∣_∣

```


## Binary recursion

```agda

rec₂ : is-prop P → (A → B → P) → ∥ A ∥ → ∥ B ∥ → P
rec₂ P-prop f =
  rec (Π-is-prop λ _ → P-prop) (λ a → rec P-prop (f a))

```


## Monadic structure

```agda

bind : ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥
bind ta f = rec squash f ta

join : ∥ ∥ A ∥ ∥ → ∥ A ∥
join = rec squash (λ x → x)

```


## Universal property

```agda

factor : is-prop P → (A → P) → (∥ A ∥ → P)
factor = rec

restrict : (∥ A ∥ → P) → (A → P)
restrict f = f ∘ ∣_∣

```
