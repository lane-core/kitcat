```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Base where

open import Lib.Core.Prim

Nt : ∀ {u v w} → {A : Type u} → (A → Type v) → (A → Type w) → Type (u ⊔ v ⊔ w)
Nt P Q = ∀ x → P x → Q x

_=>_ : ∀ {u v w} → {A : Type u} → (A → Type v) → (A → Type w) → A → Type (v ⊔ w)
_=>_ P Q = λ x → P x → Q x
infixr -1 _=>_
{-# INLINE _=>_ #-}

infixr -1 _$_ _$ₑ_ _$ᵢ_ -- _$ₛ_

_$_ : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} → ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}

@0 _$ₑ_ : ∀ {u v} {@0 A : Type u} {@0 B : @0 A → Type v} → @0 ((x : A) → B x) → ((x : A) → B x)
@0 f $ₑ x = f x
{-# INLINE _$ₑ_ #-}

_$ᵢ_ : ∀ {u v} {@0 A : Type u} {@0 B : .A → Type v} → (.(x : A) → B x) → (.(x : A) → B x)
f $ᵢ x = f x
{-# INLINE _$ᵢ_ #-}

-- _$ₛ_ : ∀ {u v} {A : Type u} {B : A → SSet v} → ((x : A) → B x) → ((x : A) → B x)
-- f $ₛ x = f x
-- {-# INLINE _$ₛ_ #-}
