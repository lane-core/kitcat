Discrete and separated types.

A type is *discrete* if it has decidable equality at every point, and
*separated* if double negation of equality implies equality. Discrete
types are separated, and separated types are sets.

Credit: TypeTopology, UF.DiscreteAndSeparated (Escardo)

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Discrete where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Dec
open Dec
open import Core.Data.Sigma
open import Core.Data.Sum
open import Core.Data.Empty
open import Core.Data.Bool
open import Core.Trait.Eq

private variable
  u v : Level
  A : Type u
  B : Type v

```

## Isolated points

A point `x : A` is isolated if equality with `x` is decidable.

```agda

is-isolated : ∀ {u} {A : Type u} → A → Type u
is-isolated {A = A} x = (y : A) → Dec (x ≡ y)

```

## Discrete types

A type is discrete if every point is isolated. This is definitionally
equal to `DecEq A`, but named for clarity.

```agda

is-discrete : ∀ {u} → Type u → Type u
is-discrete A = (x : A) → is-isolated x

```

## Separated types

A type is separated (or ¬¬-separated) if stability holds for its
identity types.

```agda

is-separated : ∀ {u} → Type u → Type u
is-separated A = (x y : A) → is-stable (x ≡ y)

```

## Discrete implies separated

```agda

is-discrete→is-separated
  : is-discrete A → is-separated A
is-discrete→is-separated d x y =
  dec→stable (d x y)

```

## Separated implies set

Separated types have collapsible identity types, hence are sets by
the Kraus--Escardo--Coquand--Altenkirch argument.

```agda

is-separated→is-set
  : is-separated A → is-set A
is-separated→is-set s =
  collapsible-id→is-set λ x y →
    stable→collapsible (s x y)

```

## Conversions

```agda

Discrete→is-discrete : Discrete A → is-discrete A
Discrete→is-discrete d x y = d .Discrete._≟_ x y

is-discrete→Discrete : is-discrete A → Discrete A
is-discrete→Discrete d .Discrete._≟_ = d

```

## Closure under products

```agda

×-is-discrete
  : is-discrete A → is-discrete B → is-discrete (A × B)
×-is-discrete dA dB (a₁ , b₁) (a₂ , b₂)
  with dA a₁ a₂ | dB b₁ b₂
... | yes p | yes q = yes (λ i → p i , q i)
... | yes _ | no ¬q = no λ r → ¬q (ap snd r)
... | no ¬p | _     = no λ r → ¬p (ap fst r)

```

## Closure under Sigma types

```agda

Σ-is-discrete
  : ∀ {u v} {A : Type u} {B : A → Type v}
  → is-discrete A
  → ((x : A) → is-discrete (B x))
  → is-discrete (Σ B)
Σ-is-discrete {B = B} dA dB (a₁ , b₁) (a₂ , b₂)
  with dA a₁ a₂
... | no ¬p = no λ r → ¬p (ap fst r)
... | yes p with dB a₂ (subst B p b₁) b₂
... | yes q = yes λ i → p i , Path-over.to-pathp {A = λ i → B (p i)} q i
... | no ¬q = no λ r →
  ¬q (sym (ap (λ e → subst B e b₁)
      (A-set (ap fst r) p))
    ∙ Path-over.from-pathp {A = λ i → B (r i .fst)} (ap snd r))
  where A-set = hedberg dA a₁ a₂

```

## Closure under coproducts

```agda

⊎-is-discrete
  : is-discrete A → is-discrete B → is-discrete (A ⊎ B)
⊎-is-discrete dA dB (inl a₁) (inl a₂)
  with dA a₁ a₂
... | yes p = yes (ap inl p)
... | no ¬p = no λ r → ¬p (⊎.inl-inj r)
⊎-is-discrete dA dB (inl _) (inr _) =
  no ⊎.disjoint
⊎-is-discrete dA dB (inr _) (inl _) =
  no λ p → ⊎.disjoint (sym p)
⊎-is-discrete dA dB (inr b₁) (inr b₂)
  with dB b₁ b₂
... | yes q = yes (ap inr q)
... | no ¬q = no λ r → ¬q (⊎.inr-inj r)

```

## Discrete trait instances

```agda

instance
  Discrete-Bool : Discrete Bool
  Discrete-Bool .Discrete._≟_ = Bool.DecEq-Bool

```
