The Maybe type with Functor, Applicative, Monad, and Alternative instances.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Data.Maybe where

open import Core.Type
open import Core.Trait.Effect
open import Core.Trait.Map
open import Core.Trait.Applicative
open import Core.Trait.Monad
open import Core.Trait.Alternative

open import Agda.Builtin.Maybe public
open import Agda.Builtin.Cubical.Path using (_≡_)

private
  module M = Effect (impl Maybe)

  refl : ∀ {u} {A : Type u} {x : A} → x ≡ x
  refl {x = x} _ = x

  funext
    : ∀ {u v} {A : Type u} {B : A → Type v} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x) → f ≡ g
  funext p i x = p x i

  _$_ : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → A → B
  f $ x = f x

  compose : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
          → (B → C) → (A → B) → A → C
  compose g f x = g (f x)

  map-maybe : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Maybe A → Maybe B
  map-maybe f nothing  = nothing
  map-maybe f (just x) = just (f x)

instance
  Map-Maybe : Map (impl Maybe)
  Map-Maybe .map = map-maybe
  Map-Maybe .map-id = funext go where
    go : ∀ {ℓ} {A : Type ℓ} (x : Maybe A) → map-maybe id x ≡ x
    go nothing  = refl
    go (just _) = refl
  Map-Maybe .map-comp {f = f} {g} = funext go where
    go : ∀ x → map-maybe (f ∘ g) x ≡ (map-maybe f ∘ map-maybe g) x
    go nothing  = refl
    go (just _) = refl

  Applicative-Maybe : Applicative (impl Maybe)
  Applicative-Maybe .Map-Applicative = Map-Maybe
  Applicative-Maybe .pure = just
  Applicative-Maybe ._<*>_ nothing  _  = nothing
  Applicative-Maybe ._<*>_ (just f) mx = map-maybe f mx
  Applicative-Maybe .pure-id {v = nothing}  = refl
  Applicative-Maybe .pure-id {v = just _}   = refl
  Applicative-Maybe .pure-∘ {u = nothing}                              = refl
  Applicative-Maybe .pure-∘ {u = just _} {v = nothing}                 = refl
  Applicative-Maybe .pure-∘ {u = just _} {v = just _} {w = nothing}    = refl
  Applicative-Maybe .pure-∘ {u = just _} {v = just _} {w = just _}     = refl
  Applicative-Maybe .pure-hom = refl
  Applicative-Maybe .pure-interchange {u = nothing} = refl
  Applicative-Maybe .pure-interchange {u = just _}  = refl

  Monad-Maybe : Monad (impl Maybe)
  Monad-Maybe .Applicative-Monad = Applicative-Maybe
  Monad-Maybe ._>>=_ nothing  _ = nothing
  Monad-Maybe ._>>=_ (just x) f = f x
  Monad-Maybe .>>=-left-id             = refl
  Monad-Maybe .>>=-right-id {m = nothing} = refl
  Monad-Maybe .>>=-right-id {m = just _}  = refl
  Monad-Maybe .>>=-assoc {m = nothing} = refl
  Monad-Maybe .>>=-assoc {m = just _}  = refl

  Alternative-Maybe : Alternative (impl Maybe)
  Alternative-Maybe .Applicative-Alternative = Applicative-Maybe
  Alternative-Maybe .empty = nothing
  Alternative-Maybe ._<|>_ nothing  y = y
  Alternative-Maybe ._<|>_ (just x) _ = just x
  Alternative-Maybe .<|>-left-id               = refl
  Alternative-Maybe .<|>-right-id {x = nothing} = refl
  Alternative-Maybe .<|>-right-id {x = just _}  = refl
  Alternative-Maybe .<|>-assoc {x = nothing} = refl
  Alternative-Maybe .<|>-assoc {x = just _}  = refl

```
