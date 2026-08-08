The shape of the unit-identification datum over the chosen-edge
carrier. The unit tier never mentions the chosen edge: it projects
its own unit, and the identification of the two is the third tier's
whole content. That content is a path in a hom type — `datum≃path`
computes it outright — so asking any equivalent packaging to be
propositional asks the loop space of the hom type to be
propositional, a truncation condition. The one-fiber-for-both-hands
candidate reduces the same way, to the path type between the two
hands' projected units. A self-referential datum closes the file:
an edge absorbing against itself in the held slot is statable over
the bare carrier, with no chosen edge at all.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.UnitShape where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Equiv.Base using (_≃_; iso→equiv; is-contr-equiv)
open import Core.Equiv.Properties using (_∙e_; esym; Σ-contr-fst; Π-contr-dom)
open import Core.HLevel.Base using (is-prop-equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Degenerate.Chosen
```

## The identification datum is a path

Given the coterm-hand unit tier, the smallest identification datum
is that the chosen edge acts as the identity action. The unit fiber
is contractible, so its component at any edge is the path space
from that edge to the centre: reassociating and contracting the two
singletons in turn computes the datum.

```agda
module shape {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn using (coact-π; act-π)

  module _ (U⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)) where

    unit⁻ : ∀ x → hom x x
    unit⁻ x = U⁻ x .center .fst

    datum : ∀ x → Type (o ⊔ h)
    datum x = coact-π (idn x) ≡ snd

    singl-contr : ∀ {x} (a : hom x x) → is-contr (Σ e ∶ hom x x , e ≡ a)
    singl-contr a .center = a , refl
    singl-contr a .paths (e , p) i = p (~ i) , λ j → p (~ i ∨ j)

    reassoc : ∀ {x} (a : hom x x)
            → (Σ t ∶ fiber (coact-π {x} {x}) snd , t .fst ≡ a)
            ≃ (Σ s ∶ (Σ e ∶ hom x x , e ≡ a) , coact-π (s .fst) ≡ snd)
    reassoc a = iso→equiv (λ ((e , q) , r) → (e , r) , q)
                          (λ ((e , r) , q) → (e , q) , r)
                          (λ _ → refl) (λ _ → refl)

    component≃path : ∀ {x} (a : hom x x) → (coact-π a ≡ snd) ≃ (unit⁻ _ ≡ a)
    component≃path a =
      esym (Σ-contr-fst (singl-contr a))
      ∙e esym (reassoc a)
      ∙e Σ-contr-fst (U⁻ _)

    datum≃path : ∀ x → datum x ≃ (unit⁻ x ≡ idn x)
    datum≃path x = component≃path (idn x)
```

Propositionality of the datum is a truncation condition on the
homs.

```agda
    datum-prop→loop-prop
      : ∀ x → is-prop (datum x) → is-prop (unit⁻ x ≡ idn x)
    datum-prop→loop-prop x pr = is-prop-equiv (esym (datum≃path x)) pr

    datum-prop→truncation
      : ∀ x → is-prop (datum x) → datum x → is-prop (idn x ≡ idn x)
    datum-prop→truncation x pr a =
      subst (λ e → is-prop (e ≡ idn x))
            (datum≃path x .fst a) (datum-prop→loop-prop x pr)
```

## One fiber carrying both absorptions

A single edge absorbing on both hands, contracted as one space, is
propositional as a statement and forces the hands to share a unit —
and the space is the path type between the two projected units, so
asserting its contractibility is again a truncation condition.
Moving the quantifier does not change what is being asserted.

```agda
    module _ (U⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) snd)) where

      unit⁺ : ∀ x → hom x x
      unit⁺ x = U⁺ x .center .fst

      reassoc⁺ : ∀ {x} (a : hom x x)
               → (Σ t ∶ fiber (act-π {x} {x}) snd , t .fst ≡ a)
               ≃ (Σ s ∶ (Σ e ∶ hom x x , e ≡ a) , act-π (s .fst) ≡ snd)
      reassoc⁺ a = iso→equiv (λ ((e , q) , r) → (e , r) , q)
                             (λ ((e , r) , q) → (e , q) , r)
                             (λ _ → refl) (λ _ → refl)

      component≃path⁺ : ∀ {x} (a : hom x x) → (act-π a ≡ snd) ≃ (unit⁺ _ ≡ a)
      component≃path⁺ a =
        esym (Σ-contr-fst (singl-contr a))
        ∙e esym (reassoc⁺ a)
        ∙e Σ-contr-fst (U⁺ _)

      both : ∀ x → Type (o ⊔ h)
      both x = Σ e ∶ hom x x , (coact-π e ≡ snd) × (act-π e ≡ snd)

      both-reassoc : ∀ x
                   → both x
                   ≃ (Σ c ∶ fiber (coact-π {x} {x}) snd , act-π (c .fst) ≡ snd)
      both-reassoc x = iso→equiv (λ (e , p , q) → (e , p) , q)
                                 (λ ((e , p) , q) → e , p , q)
                                 (λ _ → refl) (λ _ → refl)

      both≃path : ∀ x → both x ≃ (unit⁺ x ≡ unit⁻ x)
      both≃path x =
        both-reassoc x ∙e Σ-contr-fst (U⁻ x) ∙e component≃path⁺ (unit⁻ x)

      both-contr→truncation
        : ∀ x → is-contr (both x) → both x → is-contr (unit⁻ x ≡ unit⁻ x)
      both-contr→truncation x c b =
        subst (λ e → is-contr (e ≡ unit⁻ x))
              (both≃path x .fst b) (is-contr-equiv (esym (both≃path x)) c)
```

## The self-referential datum

The edge stands in its own held slot, on each hand, so the
statement mentions no chosen edge: it is a bare-carrier predicate.
Being `is-contr` of a Σ, the tier is a proposition, and its centre
projects one edge carrying both absorptions.

```agda
module self {o h} (G : virtual-graph o h) (open virtual-graph G) where

  unit-data : ob → Type (o ⊔ h)
  unit-data x =
    Σ e ∶ hom x x
    , ((t : term x)   → reflect e (t , (x , e)) ≡ t .snd)
    × ((γ : coterm x) → reflect e ((x , e) , γ) ≡ γ .snd)

  is-unital : Type (o ⊔ h)
  is-unital = ∀ x → is-contr (unit-data x)
```
