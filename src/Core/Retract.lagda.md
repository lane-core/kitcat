Retracts: bundled retract type and closure properties.

Credit: TypeTopology, UF.Retracts (Escardo)

A type `A` is a retract of `B` when there exist `s : A -> B` (section)
and `r : B -> A` (retraction) with `r . s ~ id`. This module bundles
this data as a record and develops the basic algebra of retracts:
identity, composition, closure under products and Sigma, and the
connection to equivalences and h-levels.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Retract where

open import Core.Trait.Trunc
open import Core.Data.Sigma
open import Core.Data.Nat using (Nat)
open import Core.Transport
open import Core.Type
open import Core.Base
open import Core.Equiv
open import Core.Kan

private variable
  u v w : Level
```


## Bundled retract

```agda

record _◁_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  no-eta-equality
  field
    section    : A → B
    retraction : B → A
    is-retract : (a : A) → retraction (section a) ≡ a

infix 5 _◁_
open _◁_ public
{-# INLINE _◁_.constructor #-}
```


## Identity and composition

```agda

◁-id : {A : Type u} → A ◁ A
◁-id .section    = id
◁-id .retraction = id
◁-id .is-retract = λ _ → refl

◁-comp
  : {A : Type u} {B : Type v} {C : Type w}
  → A ◁ B → B ◁ C → A ◁ C
◁-comp f g .section    = g .section ∘ f .section
◁-comp f g .retraction = f .retraction ∘ g .retraction
◁-comp f g .is-retract a =
  ap (f .retraction) (g .is-retract (f .section a))
  ∙ f .is-retract a
```


## Equivalences give retracts

```agda

module _ {u v} {A : Type u} {B : Type v} (e : A ≃ B) where
  private module E = Equiv e

  equiv→retract : A ◁ B
  equiv→retract .section    = E.fwd
  equiv→retract .retraction = E.inv
  equiv→retract .is-retract = E.unit

  equiv→retract⁻ : B ◁ A
  equiv→retract⁻ .section    = E.inv
  equiv→retract⁻ .retraction = E.fwd
  equiv→retract⁻ .is-retract = E.counit
```


## Retracts preserve h-levels

The unbundled `retract->is-hlevel` lives in `Core.Trait.Trunc`. Here
we wrap it for the bundled type: if `A` is a retract of `B`, then any
h-level of `B` transfers to `A`.

```agda

◁→is-hlevel
  : {A : Type u} {B : Type v}
  → (n : Nat) → A ◁ B → is-hlevel n B → is-hlevel n A
◁→is-hlevel n r =
  retract→is-hlevel n (r .retraction) (r .section) (r .is-retract)
```


## Retract of product types

```agda

×-◁
  : {A : Type u} {A' : Type v}
    {B : Type u} {B' : Type v}
  → A ◁ A' → B ◁ B' → (A × B) ◁ (A' × B')
×-◁ rA rB .section    (a , b) = rA .section a , rB .section b
×-◁ rA rB .retraction (a , b) = rA .retraction a , rB .retraction b
×-◁ rA rB .is-retract (a , b) i =
  rA .is-retract a i , rB .is-retract b i
```


## Retract of Sigma types

Given `rA : A retract A'` and a fiberwise retract indexed over `A'`,
the total spaces form a retract. The fiberwise condition is indexed
over `A'` (not `A`) because the retraction of a total pair `(a', b')`
must produce a fiber over `retraction rA a'`, and we need to retract
`B' a'` into that fiber directly.

```agda

Σ-◁
  : {A : Type u} {A' : Type v}
    {B : A → Type w} {B' : A' → Type w}
  → (rA : A ◁ A')
  → ((a' : A') → B (rA .retraction a') ◁ B' a')
  → Σ B ◁ Σ B'
Σ-◁ {B = B} rA rB .section (a , b) =
  s a , rB (s a) .section (subst B (sym (h a)) b)
  where s = rA .section; h = rA .is-retract
Σ-◁ rA rB .retraction (a' , b') =
  rA .retraction a' , rB a' .retraction b'
Σ-◁ {B = B} rA rB .is-retract (a , b) i =
  h a i , snd-path i where
  s  = rA .section
  r  = rA .retraction
  h  = rA .is-retract

  x : B (r (s a))
  x = subst B (sym (h a)) b

  pathover
    : coe01 (λ i → B (h a i))
        (rB (s a) .retraction (rB (s a) .section x))
      ≡ b
  pathover =
    ap (coe01 (λ i → B (h a i))) (rB (s a) .is-retract x)
    ∙ transport⁻-transport (ap B (h a)) b

  snd-path
    : PathP (λ i → B (h a i))
        (rB (s a) .retraction (rB (s a) .section x)) b
  snd-path = Path-over.to-pathp pathover
```
