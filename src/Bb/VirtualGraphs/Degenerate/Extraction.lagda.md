One half-twist posits the other. The negative absorption tier mentions
`coact-π`, hence `var`, hence `rx` alone — so it is stateable
before a positive half-twist exists, and its centre defines one. Mutual
inverseness on that side is then the centre's own witness, not an
axiom. The telescope is group O: the carrier, `rx`, and the
tier; the positive family is a definition.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Extraction where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
```

## The extraction

```agda
module extraction {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x)
  (U⁻ : absorbing⁻.is-absorbing⁻ G rx) where

  open framing⁻ G rx public

  corx : (x : ob) → hom x x
  corx x = U⁻ x .center .fst

  cancel⁻ : (x : ob) → coact-π {x} {x} (corx x) ≡ snd
  cancel⁻ x = U⁻ x .center .snd

  open framing⁺ G corx public
  open absorbing⁺ G corx public
```

The coterm-side absorption comes with the extraction, with no
readback and no second half-twist posited.

```agda
  absorb⁻ : ∀ {x} (k : coterm x) → coact (corx x) k ≡ k
  absorb⁻ = from-cancel.absorb⁻ G rx corx corx cancel⁻
```

## What comes free over the positive hand

```agda
  module theory (S : reflect-is-embedding G) (C⁺ : is-composable⁺) where

    open tower⁺ G rx S C⁺ using (_⨾⁺_; reflect-⨾⁺)

    composite-corx : ∀ {x y} (f : hom x y)
                     → composite⁺ f (corx y) ≡ reflect f
    composite-corx f i γ = reflect f (γ .fst , absorb⁻ (γ .snd) i)

    unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ corx y ≡ f
    unitr⁺ {x} {y} f =
      reflect-lc G S (reflect-⨾⁺ f (corx y) ∙ composite-corx f)
```

## The positive tier over the extracted framing

Its centre is a left unit for the negative cut, and the term-side
cancellation at the posited half-twist is equivalent to that centre
agreeing with it. The twice-opposed carrier posits the centre, so
the same equivalence reads: the opposite is involutive at the half-twist
field.

```agda
  module system⁻ (S : reflect-is-embedding G) (C⁺ : is-composable⁺) (C⁻ : is-composable⁻)
    (U⁺ : is-absorbing⁺) where

    open theory S C⁺ public
    open tower⁻ G corx S C⁻ using (_⨾⁻_; reflect-⨾⁻)

    centre⁺ : (x : ob) → hom x x
    centre⁺ x = U⁺ x .center .fst

    centre-cancel⁺ : (x : ob) → act-π {x} {x} (centre⁺ x) ≡ snd
    centre-cancel⁺ x = U⁺ x .center .snd

    absorb⁺ : ∀ {x} (t : term x) → act (centre⁺ x) t ≡ t
    absorb⁺ = from-cancel.absorb⁺ G rx corx centre⁺ centre-cancel⁺

    composite-centre⁺ : ∀ {x y} (g : hom x y)
                      → composite⁻ (centre⁺ x) g ≡ reflect g
    composite-centre⁺ g i γ = reflect g (absorb⁺ (γ .fst) i , γ .snd)

    unitl⁻ : ∀ {x y} (g : hom x y) → centre⁺ x ⨾⁻ g ≡ g
    unitl⁻ {x} g =
      reflect-lc G S (reflect-⨾⁻ (centre⁺ x) g ∙ composite-centre⁺ g)

    cancel⁺ : Type (o ⊔ h)
    cancel⁺ = ∀ x → act-π {x} {x} (rx x) ≡ snd

    agree : Type (o ⊔ h)
    agree = ∀ x → centre⁺ x ≡ rx x

    cancel⁺→agree : cancel⁺ → agree
    cancel⁺→agree c x = ap fst (U⁺ x .paths (rx x , c x))

    agree→cancel⁺ : agree → cancel⁺
    agree→cancel⁺ p x =
      subst (λ e → act-π {x} {x} e ≡ snd) (p x) (centre-cancel⁺ x)
```

The telescope is inhabited with `agree` refutable: the Klein
four-group under a three-cycle-half-twisted reflection inhabits every
hypothesis while the positive centre lands one step past the posited
half-twist. In every abelian-group model the centre is the double
inverse, so `cancel⁺` holds there — the separation needs a half-twisted
reflection.
