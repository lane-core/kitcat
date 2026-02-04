General-purpose function combinators.

Adapted from agda-prelude, Prelude.Function
(Ulf Norell; January 2026).

```agda
{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Function.Base where

open import Core.Type

flip
  : ∀ {u v w}
    {@0 A : Type u} {@0 B : Type v} {@0 C : A → B → Type w}
  → (∀ x y → C x y) → ∀ y x → C x y
flip f y x = f x y
{-# INLINE flip #-}

_$_ : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v}
    → (∀ x → B x) → ∀ x → B x
f $ x = f x
infixr -20 _$_
{-# INLINE _$_ #-}

_$′_ : ∀ {u v} {@0 A : Type u} {@0 B : Type v}
     → (A → B) → A → B
f $′ x = f x
infixr -20 _$′_
{-# INLINE _$′_ #-}

case_of_ : ∀ {u v} {@0 A : Type u} {@0 B : Type v}
         → A → (A → B) → B
case x of f = f x
infixr 0 case_of_
{-# INLINE case_of_ #-}

case_return_of_
  : ∀ {u v} {@0 A : Type u}
  → (x : A) → (@0 B : A → Type v) → (∀ x → B x) → B x
case x return B of f = f x
infixr 0 case_return_of_
{-# INLINE case_return_of_ #-}

_on_
  : ∀ {u v w}
    {@0 A : Type u} {@0 B : A → Type v}
    {@0 C : ∀ x y → B x → B y → Type w}
  → (∀ {x y} (bx : B x) (by : B y) → C x y bx by)
  → (f : ∀ x → B x) → ∀ x y → C x y (f x) (f y)
_*_ on f = λ x y → f x * f y
infixl 8 _on_
{-# INLINE _on_ #-}
```


## Instance helpers

```agda
it : ∀ {u} {@0 A : Type u} ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x
{-# INLINE it #-}

asInstance
  : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v}
  → (x : A) → (⦃ A ⦄ → B x) → B x
asInstance x f = f ⦃ x ⦄
{-# INLINE asInstance #-}

record Instance {u} (A : Type u) : Type u where
  constructor !
  field ⦃ x ⦄ : A

mkInstance : ∀ {u} {@0 A : Type u} → A → Instance A
mkInstance a = ! ⦃ a ⦄
{-# INLINE mkInstance #-}
```
