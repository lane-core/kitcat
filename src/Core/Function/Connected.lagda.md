Connected types and maps.

A type is connected (or 0-connected, or path-connected) when its propositional
truncation is contractible. Intuitively, this means the type is non-empty and
any two points can be connected by a path (in a proof-irrelevant sense).

A map is connected when all its fibers are connected. Connected maps are
necessarily surjective: every point in the codomain has a preimage.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Function.Connected where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.HLevel
open import Core.Data.Trunc
open Core.Data.Trunc.Trunc
open import Core.Function.Surjection
open import Core.Transport.Properties
  using (prop-inhabited→is-contr; is-contr-is-prop; is-contr→is-prop; is-prop→is-set)

private variable
  u v : Level
  A B : Type u
```


## Connected types

A type is connected when its propositional truncation is contractible.
Equivalently, a type is connected when:
1. It is merely inhabited (has a point), and
2. Any two points are merely equal (there exists a path between them).

The propositional truncation collapses the "choice" involved in picking
witnesses, leaving only the contractibility condition.

```agda

is-connected : Type u → Type u
is-connected A = is-contr ∥ A ∥

-- Being connected is a proposition
is-connected-is-prop : (A : Type u) → is-prop (is-connected A)
is-connected-is-prop A = is-contr-is-prop ∥ A ∥

-- Connected types are merely inhabited
connected→inhabited : is-connected A → ∥ A ∥
connected→inhabited c = c .center
```


## Connected maps

A map is connected when all its fibers are connected. This is stronger than
surjectivity: not only does every point have a preimage, but the space of
all preimages (with their paths) is merely contractible.

```agda

is-connected-map : {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
is-connected-map f = ∀ b → is-connected (fiber f b)

-- Being a connected map is a proposition
is-connected-map-is-prop
  : {A : Type u} {B : Type v} (f : A → B)
  → is-prop (is-connected-map f)
is-connected-map-is-prop f = Π-is-prop (λ b → is-contr-is-prop _)
```


## Connections to surjectivity

Every connected map is surjective. The converse does not hold in general:
surjectivity only requires that fibers are inhabited, while connectedness
requires that the truncation of each fiber is contractible.

```agda

-- Connected maps are surjective
connected-map→surjective
  : {A : Type u} {B : Type v} {f : A → B}
  → is-connected-map f → is-surjective f
connected-map→surjective conn b = conn b .center
```


## Preservation by equivalences

Equivalences preserve and reflect connectedness.

```agda

-- If A ≃ B and A is connected, then B is connected
-- The truncation of an equivalence is an equivalence, so ∥ A ∥ ≃ ∥ B ∥
equiv→is-connected : A ≃ B → is-connected A → is-connected B
equiv→is-connected e conn .center = map (Equiv.fwd e) (conn .center)
equiv→is-connected e conn .paths y = squash _ y

-- The converse: if A ≃ B and B is connected, then A is connected
equiv→is-connected' : A ≃ B → is-connected B → is-connected A
equiv→is-connected' e = equiv→is-connected (esym e)
```


## Surjections between connected types

When the domain is connected and we have a surjection, the codomain is
connected. More specifically, any map from a connected type to any type
is "connected enough" to ensure surjectivity when both domain and
codomain are connected.

```agda

-- A type is connected iff any map to a proposition factors through the point
-- This is the universal property of connected types for propositions

-- If A is connected and B is a prop, then A → B is equivalent to B
-- (A connected type "evaluates" all propositions to their value)
connected-to-prop
  : is-connected A → is-prop B → (A → B) → B
connected-to-prop conn prop f = rec prop f (conn .center)

-- NOTE: The proposition "connected A → connected B → (f : A → B) → is-surjective f"
-- is FALSE in general. Counterexample: let A = B = Bool (which is connected since
-- ∥ Bool ∥ is contractible), and let f be the constant function at true.
-- Then fiber f false is empty, so f is not surjective.
--
-- What IS true is that connected maps are surjective (proven above), and that
-- equivalences between connected types are surjective (trivially, as all
-- equivalences are surjective).

-- For the specified lemma, we provide a weaker version that is actually provable:
-- If B is a proposition, then any map from a connected type to B is surjective
-- (in fact, constant).
connected-to-prop-surjective
  : is-connected A → is-prop B → (f : A → B) → is-surjective f
connected-to-prop-surjective connA bprop f b =
  rec squash (λ a → ∣ a , bprop (f a) b ∣) (connA .center)
```


## Identity is a connected map

The identity function is trivially connected since its fibers are singletons.

```agda

id-is-connected : is-connected-map (idfun A)
id-is-connected {A = A} a .center = ∣ a , refl ∣
id-is-connected {A = A} a .paths y = prop _ y
```


## Composition of connected maps

Connected maps are closed under composition.

```agda

-- Connected maps are closed under composition.
-- The proof uses that the fiber of g ∘ f over c decomposes as:
--   fiber (g ∘ f) c ≃ Σ (b : B), fiber f b × (g b ≡ c)
-- When both f and g have connected fibers, this total space has connected
-- truncation.
connected-map-comp
  : {A : Type u} {B C : Type v}
  → {f : A → B} {g : B → C}
  → is-connected-map f → is-connected-map g
  → is-connected-map (g ∘ f)
connected-map-comp {f = f} {g = g} connf conng c .center =
  rec squash
    (λ { (b , q) → map (λ { (a , p) → a , ap g p ∙ q }) (connf b .center) })
    (conng c .center)
connected-map-comp {f = f} {g = g} connf conng c .paths y = prop _ y
```
