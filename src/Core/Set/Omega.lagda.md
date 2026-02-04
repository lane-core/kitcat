The subtype classifier and its lattice operations.

This module uses `--cubical` (not `--erased-cubical`) because `Omega-ext`
requires propositional extensionality, which depends on `ua` from
`Core.Univalence`.

Credit: TypeTopology, UF.SubtypeClassifier (Escardo)

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Core.Set.Omega where

open import Core.Data.Sigma
open import Core.Data.Trunc
open import Core.Data.Empty
open import Core.Data.Sum
open import Core.HLevel
open import Core.Set
open import Core.Base
open import Core.Type
open import Core.Kan

private variable
  u v : Level
```


## The Subtype Classifier

The subtype classifier `Omega` is the type of all propositions. It classifies
subtypes of a type `A` via maps `A -> Omega u`, following Escardo's
TypeTopology formulation.

```agda

Omega : (u : Level) -> Type (u ₊)
Omega = Prop
```


## Projections

```agda

_holds : Prop u -> Type u
P holds = ∣ P ∣ᴾ

holds-is-prop : (P : Prop u) -> is-prop (P holds)
holds-is-prop P = P .has-is-prop
```


## Propositional Extensionality for Omega

Two propositions in `Omega` are equal when they are logically equivalent.
This is a direct lift of `prop-iff` from `Core.Set`.

```agda

Omega-ext
  : {P Q : Omega u}
  -> (P holds -> Q holds) -> (Q holds -> P holds)
  -> P ≡ Q
Omega-ext {P = P} {Q} f g = prop-iff P Q f g
```


## Lattice Operations

Universe-polymorphic top and bottom propositions, conjunction, negation,
and implication.

```agda

topOmega : Omega u
topOmega .∣_∣ᴾ = Unit
topOmega .has-is-prop _ _ = refl

botOmega : Omega u
botOmega .∣_∣ᴾ = Lift _ ⊥
botOmega .has-is-prop (liftℓ ())

_∧Omega_ : Omega u -> Omega u -> Omega u
(P ∧Omega Q) .∣_∣ᴾ = (P holds) × (Q holds)
(P ∧Omega Q) .has-is-prop =
  is-prop-× (holds-is-prop P) (holds-is-prop Q)

infixr 6 _∧Omega_

notOmega : Omega u -> Omega u
notOmega P .∣_∣ᴾ = P holds -> ⊥
notOmega P .has-is-prop = Π-is-prop λ _ -> ⊥-elim
  where
    ⊥-elim : is-prop ⊥
    ⊥-elim ()

_→Omega_ : Omega u -> Omega v -> Omega (u ⊔ v)
(P →Omega Q) .∣_∣ᴾ = P holds -> Q holds
(P →Omega Q) .has-is-prop =
  Π-is-prop λ _ -> holds-is-prop Q

infixr 5 _→Omega_
```


## Disjunction

Disjunction requires propositional truncation of the coproduct.

```agda

_∨Omega_ : Omega u -> Omega u -> Omega u
(P ∨Omega Q) .∣_∣ᴾ = ∥ P holds ⊎ Q holds ∥
(P ∨Omega Q) .has-is-prop = squash

infixr 5 _∨Omega_
```
