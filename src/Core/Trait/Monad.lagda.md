Monad trait: types with sequential composition via bind.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Monad where

open import Core.Type using (Level; Type; Typeω; _⊔_)
open import Core.Base using (_≡_)
open import Core.Trait.Effect
open import Core.Trait.Map
open import Core.Trait.Applicative

```

A monad extends Applicative with `_>>=_` (bind), enabling sequential effectful
computation where each step can depend on the result of the previous one.
The three monad laws ensure bind behaves coherently with `pure`.

Following the 1lab `Meta.Idiom.Monad` pattern, enabling universe-polymorphic
monads via the `Effect` abstraction.

```agda

record Monad (M : Effect) : Typeω where
  no-eta-equality
  private module M = Effect M
  field
    ⦃ Applicative-Monad ⦄ : Applicative M
    _>>=_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → (A → M.₀ B) → M.₀ B

  infixl 1 _>>=_

  private
    p : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    p = pure Applicative-Monad

  field
    @0 >>=-left-id : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                   → {a : A} {f : A → M.₀ B}
                   → (p a >>= f) ≡ f a
    @0 >>=-right-id : ∀ {ℓ} {A : Type ℓ}
                    → {m : M.₀ A}
                    → (m >>= p) ≡ m
    @0 >>=-assoc : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
                 → {m : M.₀ A} {f : A → M.₀ B} {g : B → M.₀ C}
                 → ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))

open Monad public
{-# INLINE Monad.constructor #-}

```

Standard monad operators following Haskell/Idris conventions.

```agda

module _ {M : Effect} ⦃ mon : Monad M ⦄ where
  private module M = Effect M
  private
    _>>>=_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → (A → M.₀ B) → M.₀ B
    _>>>=_ = _>>=_ mon

  infixl 1 _>>_
  infixr 1 _=<<_ _>=>_ _<=<_

  _>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → M.₀ B → M.₀ B
  ma >> mb = ma >>>= λ _ → mb

  _=<<_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → M.₀ B) → M.₀ A → M.₀ B
  f =<< ma = ma >>>= f

  join : ∀ {ℓ} {A : Type ℓ} → M.₀ (M.₀ A) → M.₀ A
  join mma = mma >>>= λ ma → ma

  _>=>_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        → (A → M.₀ B) → (B → M.₀ C) → A → M.₀ C
  (f >=> g) a = f a >>>= g

  _<=<_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        → (B → M.₀ C) → (A → M.₀ B) → A → M.₀ C
  (g <=< f) a = f a >>>= g

```
