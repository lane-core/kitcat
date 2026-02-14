Bundled group type for mathematical group theory.

This provides a self-contained `Grp` record with non-erased proof fields,
suitable for reasoning about groups as first-class mathematical objects.
The `Grp-inst` module derives lightweight `Core.Trait` instances so that
code written against the trait hierarchy works seamlessly with `Grp`
carriers.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Base where

open import Core.Trait.Group
open import Core.Trait.Trunc
open import Core.Data.Nat.Type using (S)
open import Core.Base using (_≡_; is-set)
open import Core.Type

private variable
  u : Level
```


## The bundled group record

```agda

record Grp (u : Level) : Type (u ₊) where
  no-eta-equality
  infixl 7 _·_
  field
    Carrier    : Type u
    _·_        : Carrier → Carrier → Carrier
    e          : Carrier
    inv        : Carrier → Carrier
    assoc      : ∀ x y z → (x · y) · z ≡ x · (y · z)
    idl        : ∀ x → e · x ≡ x
    idr        : ∀ x → x · e ≡ x
    invl       : ∀ x → inv x · x ≡ e
    invr       : ∀ x → x · inv x ≡ e
    has-is-set : is-set Carrier

open Grp public
{-# INLINE Grp.constructor #-}

```


## Instances

```agda

instance
  Underlying-Grp : Underlying (Grp u)
  Underlying-Grp .ℓ-underlying = _
  Underlying-Grp .⌞_⌟ = Carrier

  Trunc-Grp : ∀ {G : Grp u} {k} → Trunc (Carrier G) (S (S k))
  Trunc-Grp {G = G} = set-trunc (has-is-set G)

```


## Deriving trait instances

Given a `Grp`, the carrier automatically gets `Semigroup`, `Monoid`, and
`Group` instances. This lets code written against the trait hierarchy use
`Grp` carriers without manual plumbing.

```agda

module Grp-inst (G : Grp u) where
  private
    C = Carrier G

  instance
    Semigroup-Grp : Semigroup C
    Semigroup-Grp ._<>_ = G ._·_
    Semigroup-Grp .sassoc = G .assoc

    Monoid-Grp : Monoid C
    Monoid-Grp .Monoid.Semigroup-Monoid = Semigroup-Grp
    Monoid-Grp .mempty = e G
    Monoid-Grp .munitl = idl G
    Monoid-Grp .munitr = idr G

    Group-Grp : Group C
    Group-Grp .Group.Monoid-Group = Monoid-Grp
    Group-Grp .ginv = inv G
    Group-Grp .ginvl = invl G
    Group-Grp .ginvr = invr G

```


## Smart constructor

```agda

make-grp
  : (C : Type u) (_·_ : C → C → C) (e : C) (inv : C → C)
  → (∀ x y z → (x · y) · z ≡ x · (y · z))
  → (∀ x → e · x ≡ x)
  → (∀ x → x · e ≡ x)
  → (∀ x → inv x · x ≡ e)
  → (∀ x → x · inv x ≡ e)
  → is-set C
  → Grp u
make-grp C _·_ e inv assoc idl idr invl invr set .Carrier = C
make-grp C _·_ e inv assoc idl idr invl invr set ._·_ = _·_
make-grp C _·_ e inv assoc idl idr invl invr set .Grp.e = e
make-grp C _·_ e inv assoc idl idr invl invr set .Grp.inv = inv
make-grp C _·_ e inv assoc idl idr invl invr set .Grp.assoc = assoc
make-grp C _·_ e inv assoc idl idr invl invr set .Grp.idl = idl
make-grp C _·_ e inv assoc idl idr invl invr set .Grp.idr = idr
make-grp C _·_ e inv assoc idl idr invl invr set .Grp.invl = invl
make-grp C _·_ e inv assoc idl idr invl invr set .Grp.invr = invr
make-grp C _·_ e inv assoc idl idr invl invr set .has-is-set = set
```
