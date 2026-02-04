Properties of coproducts.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Sum.Properties where

open import Core.Base
open import Core.Type
open import Core.Transport
open import Core.Data.Empty
open import Core.Data.Sum.Type
open import Core.Data.Sum.Base

private variable
  u v w x y z : Level
  A : Type u
  B : Type v
  C : Type w
  D : Type x
  E : Type y
  F : Type z

```

## Constructor properties

The constructors `inl` and `inr` are injective and disjoint.

```agda

private
  from-inl : {A : Type u} {B : Type v} → A → A ⊎ B → A
  from-inl d (inl a) = a
  from-inl d (inr _) = d

  from-inr : {A : Type u} {B : Type v} → B → A ⊎ B → B
  from-inr d (inl _) = d
  from-inr d (inr b) = b

inl-inj : {a a' : A} → inl {B = B} a ≡ inl a' → a ≡ a'
inl-inj {a = a} p = ap (from-inl a) p

inr-inj : {b b' : B} → inr {A = A} b ≡ inr b' → b ≡ b'
inr-inj {b = b} p = ap (from-inr b) p

disjoint : {a : A} {b : B} → inl a ≡ inr b → ⊥
disjoint p = subst f p tt where
  f : A ⊎ B → Type
  f (inl _) = ⊤
  f (inr _) = ⊥

```

## Swap

```agda

module swap where
  invol : ∀ (x : A ⊎ B) → swap (swap x) ≡ x
  invol (inl _) = refl
  invol (inr _) = refl

```

## Map

```agda

module map where
  id-id : ∀ (x : A ⊎ B) → map id id x ≡ x
  id-id (inl _) = refl
  id-id (inr _) = refl

  comp
    : (f : A → C) (g : C → E)
      (h : B → D) (k : D → F)
      (x : A ⊎ B)
    → map (g ∘ f) (k ∘ h) x ≡ map g k (map f h x)
  comp f g h k (inl _) = refl
  comp f g h k (inr _) = refl

```
