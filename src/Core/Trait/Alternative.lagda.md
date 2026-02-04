Alternative trait: applicative functors with monoid structure.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Trait.Alternative where

open import Core.Type using (Level; Type; Typeω; _⊔_; ⊤; tt)
open import Core.Base using (_≡_)
open import Core.Data.Bool using (Bool; module Bool)
open import Core.Trait.Effect
open import Core.Trait.Map
open import Core.Trait.Applicative

```

An alternative functor extends Applicative with a monoidal structure: `empty`
(identity) and `_<|>_` (choice/alternation). This captures computations that can
fail and be combined, such as parsers, optional values, and non-deterministic
computations.

The laws ensure `empty` and `_<|>_` form a monoid:
- Left identity: `empty <|> x ≡ x`
- Right identity: `x <|> empty ≡ x`
- Associativity: `(x <|> y) <|> z ≡ x <|> (y <|> z)`

```agda

record Alternative (M : Effect) : Typeω where
  no-eta-equality
  private module M = Effect M
  field
    ⦃ Applicative-Alternative ⦄ : Applicative M
    empty : ∀ {ℓ} {A : Type ℓ} → M.₀ A
    _<|>_ : ∀ {ℓ} {A : Type ℓ} → M.₀ A → M.₀ A → M.₀ A

  infixl 3 _<|>_

  field
    @0 <|>-left-id  : ∀ {ℓ} {A : Type ℓ} {x : M.₀ A}
                    → (empty <|> x) ≡ x
    @0 <|>-right-id : ∀ {ℓ} {A : Type ℓ} {x : M.₀ A}
                    → (x <|> empty) ≡ x
    @0 <|>-assoc    : ∀ {ℓ} {A : Type ℓ} {x y z : M.₀ A}
                    → ((x <|> y) <|> z) ≡ (x <|> (y <|> z))

open Alternative public
{-# INLINE Alternative.constructor #-}

```

```agda

module _ {M : Effect} ⦃ alt : Alternative M ⦄ where
  private module M = Effect M
  private
    p : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    p = pure (Applicative-Alternative alt)

  guard : Bool → M.₀ ⊤
  guard b = Bool.if-then-else b (p tt) (empty alt)

```
