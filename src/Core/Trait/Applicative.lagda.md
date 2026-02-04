Applicative trait: types with pure and sequential application.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Applicative where

open import Core.Type using (Level; Type; Typeω; _⊔_; id; const; ⊤; tt)
open import Core.Base using (_≡_)
open import Core.Data.Bool using (Bool; module Bool)
open import Core.Trait.Effect
open import Core.Trait.Map

```

```agda

private
  _$_ : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → A → B
  f $ x = f x
  {-# INLINE _$_ #-}

  compose : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
          → (B → C) → (A → B) → A → C
  compose g f x = g (f x)
  {-# INLINE compose #-}

```

An applicative functor extends Map with `pure` (embedding values) and `<*>`
(sequential application). This enables effectful computation while maintaining
structure. The laws ensure `pure` and `<*>` interact coherently.

Following the 1lab `Meta.Idiom.Applicative` pattern, enabling universe-polymorphic
applicative functors via the `Effect` abstraction.

```agda

record Applicative (M : Effect) : Typeω where
  no-eta-equality
  private module M = Effect M
  field
    ⦃ Map-Applicative ⦄ : Map M
    pure  : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    _<*>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_

  field
    @0 pure-id : ∀ {ℓ} {A : Type ℓ} {v : M.₀ A}
               → (pure id <*> v) ≡ v
    @0 pure-∘ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
              → {u : M.₀ (B → C)} {v : M.₀ (A → B)} {w : M.₀ A}
              → ((((pure compose) <*> u) <*> v) <*> w) ≡ (u <*> (v <*> w))
    @0 pure-hom : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                → {f : A → B} {x : A}
                → (pure f <*> pure x) ≡ pure (f x)
    @0 pure-interchange : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                        → {u : M.₀ (A → B)} {y : A}
                        → (u <*> pure y) ≡ (pure (_$ y) <*> u)

open Applicative public
{-# INLINE Applicative.constructor #-}

```

Standard applicative operators following Haskell/Idris conventions.

```agda

module _ {M : Effect} ⦃ app : Applicative M ⦄ where
  private module M = Effect M
  private
    p : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    p = pure app
    infixl 4 _⊛_
    _⊛_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ (A → B) → M.₀ A → M.₀ B
    _⊛_ = _<*>_ app

  infixl 4 _*>_ _<*_

  _*>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → M.₀ B → M.₀ B
  ma *> mb = p (const id) ⊛ ma ⊛ mb

  _<*_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → M.₀ B → M.₀ A
  ma <* mb = p const ⊛ ma ⊛ mb

  when : Bool → M.₀ ⊤ → M.₀ ⊤
  when b m = Bool.if-then-else b m (p tt)

  unless : Bool → M.₀ ⊤ → M.₀ ⊤
  unless b m = Bool.if-then-else b (p tt) m

```
