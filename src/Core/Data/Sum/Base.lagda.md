Operations on coproducts.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Sum.Base where

open import Core.Type
open import Core.Data.Sum.Type

ind : ∀ {u v w} {@0 A : Type u} {@0 B : Type v}
    (P : A ⊎ B → Type w)
    → (∀ a → P (inl a))
    → (∀ b → P (inr b))
    → ∀ x → P x
ind P l r (inl a) = l a
ind P l r (inr b) = r b
{-# INLINE ind #-}

rec : ∀ {u v w} {@0 A : Type u} {@0 B : Type v} {@0 C : Type w}
    → (A → C) → (B → C) → A ⊎ B → C
rec f g (inl a) = f a
rec f g (inr b) = g b
{-# INLINE rec #-}

map : ∀ {u v u' v'} {@0 A : Type u} {@0 B : Type v}
    {@0 C : Type u'} {@0 D : Type v'}
    → (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f g (inl a) = inl (f a)
map f g (inr b) = inr (g b)
{-# INLINE map #-}

map-l : ∀ {u v u'} {@0 A : Type u} {@0 B : Type v} {@0 C : Type u'}
      → (A → C) → A ⊎ B → C ⊎ B
map-l f = map f id
{-# INLINE map-l #-}

map-r : ∀ {u v v'} {@0 A : Type u} {@0 B : Type v} {@0 D : Type v'}
      → (B → D) → A ⊎ B → A ⊎ D
map-r g = map id g
{-# INLINE map-r #-}

swap : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A ⊎ B → B ⊎ A
swap (inl a) = inr a
swap (inr b) = inl b
{-# INLINE swap #-}

```
