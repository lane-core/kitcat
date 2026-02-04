Elimination principles and basic operations on W-types.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.W.Base where

open import Core.Type
open import Core.Data.Empty

open import Data.W.Type

ind
  : ∀ {u v w} {A : Type u} {B : A -> Type v}
  -> (P : W A B -> Type w)
  -> (step : (a : A) (f : B a -> W A B)
     -> ((b : B a) -> P (f b)) -> P (sup a f))
  -> (w : W A B) -> P w
ind P step (sup a f) = step a f (λ b -> ind P step (f b))

rec
  : ∀ {u v w} {A : Type u} {B : A -> Type v} {C : Type w}
  -> (step : (a : A) -> (B a -> C) -> C)
  -> W A B -> C
rec step = ind (λ _ -> _) (λ a _ -> step a)

label : ∀ {u v} {A : Type u} {B : A -> Type v}
      -> W A B -> A
label (sup a _) = a
{-# INLINE label #-}

children : ∀ {u v} {A : Type u} {B : A -> Type v}
         -> (w : W A B) -> B (label w) -> W A B
children (sup _ f) = f
{-# INLINE children #-}

```

Helper for W-types with empty arity. The library's `ex-falso` takes an erased
argument; this version does not.

```agda

absurd : ∀ {u} {A : Type u} -> ⊥ -> A
absurd ()

```
