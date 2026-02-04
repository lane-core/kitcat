The opposite group reverses multiplication. A group is abelian exactly
when it is isomorphic to its opposite via the identity function.

Adapted from TypeTopology, Groups.Opposite.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Opposite where

open import Core.Data.Sigma using (_,_)
open import Core.Base using (_≡_; refl; sym)
open import Core.Type using (Level; Type; id; ⌞_⌟)

open import Lib.Group.Base
open import Lib.Group.Hom
open import Lib.Group.Iso

private variable
  u v : Level
```


## Opposite group

The opposite (or *reverse*) group has the same carrier, unit, and
inverse, but multiplication is performed in the opposite order.

```agda

_ᵒᵖ : Grp u → Grp u
(G ᵒᵖ) .Carrier    = Carrier G
(G ᵒᵖ) ._·_ x y   = G ._·_ y x
(G ᵒᵖ) .e          = e G
(G ᵒᵖ) .inv        = inv G
(G ᵒᵖ) .assoc x y z = sym (assoc G z y x)
(G ᵒᵖ) .idl        = idr G
(G ᵒᵖ) .idr        = idl G
(G ᵒᵖ) .invl       = invr G
(G ᵒᵖ) .invr       = invl G
(G ᵒᵖ) .has-is-set = has-is-set G

```


## Abelian groups

A group is abelian when its multiplication is commutative.

```agda

is-abelian : Grp u → Type u
is-abelian G = ∀ x y → G ._·_ x y ≡ G ._·_ y x

```


## Functorial action on homomorphisms

A homomorphism `f : G -> H` is also a homomorphism `G op -> H op`:
the condition `f (y * x) = f y * f x` follows directly from the
original homomorphism condition applied to swapped arguments.

```agda

op-functoriality
  : (G : Grp u) (H : Grp v) (f : ⌞ G ⌟ → ⌞ H ⌟)
  → is-hom G H f → is-hom (G ᵒᵖ) (H ᵒᵖ) f
op-functoriality G H f μ x y = μ y x

```


## Double opposite is the original

Reversing multiplication twice gives back the original operation,
so the identity function is an isomorphism `G -> (G op) op`.

```agda

opposite-idempotent : (G : Grp u) → G ≅ ((G ᵒᵖ) ᵒᵖ)
opposite-idempotent G = id , iso where
  iso : is-iso G ((G ᵒᵖ) ᵒᵖ) id
  iso .f-is-hom _ _ = refl
  iso .g            = id
  iso .g-is-hom _ _ = refl
  iso .unit _       = refl
  iso .counit _     = refl

```


## Abelian groups and the opposite

A group is abelian exactly when the identity is a homomorphism into
the opposite group. The two directions are logically the same
statement, since `is-hom G (G op) id` unfolds to commutativity.

```agda

abelian→op-hom
  : (G : Grp u) → is-abelian G → is-hom G (G ᵒᵖ) id
abelian→op-hom G ab x y = ab x y

op-hom→abelian
  : (G : Grp u) → is-hom G (G ᵒᵖ) id → is-abelian G
op-hom→abelian G h x y = h x y
```
