The cancellation layer: readback plus the two absorption tiers. Each
tier's centre reads back as the other half-twist, so both cancellations
are theorems, the half-twist absorptions follow, and each hand gains its
other unit law — two unital magmoids on one graph, offset by the
double half-twist. The centre and cancellation fragment consumes no cut
and no embedding-condition hypothesis; the far unit laws add one
cut per hand; at contractible cuts the embedding condition is a
theorem and `associates` holds at the half-twist-flanked word. The
polarity collapse closes the file: the two half-twist conditions imply
each other at every object, so the two polarities are logically
equivalent.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Cancellation where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥; ¬_)
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Degenerate.Readback
open import Bb.VirtualGraphs.Polarity
```

## Centres and cancellations

No cut enters: readback alone reads each tier's centre at the other
half-twist's coterm or term.

```agda
module cancellation {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (R : framing.readback-of G rx corx)
  (T⁻ : absorbing⁻.is-absorbing⁻ G rx)
  (T⁺ : absorbing⁺.is-absorbing⁺ G corx) where

  open framing G rx corx

  centre⁻-corx : ∀ x → T⁻ x .center .fst ≡ corx x
  centre⁻-corx x =
      sym (R (T⁻ x .center .fst))
    ∙ happly (T⁻ x .center .snd) (x , corx x)

  centre⁺-rx : ∀ x → T⁺ x .center .fst ≡ rx x
  centre⁺-rx x =
      sym (R (T⁺ x .center .fst))
    ∙ happly (T⁺ x .center .snd) (x , rx x)

  cancel⁻ : ∀ x → coact-π (corx x) ≡ snd
  cancel⁻ x =
    subst (λ e → coact-π e ≡ snd) (centre⁻-corx x) (T⁻ x .center .snd)

  cancel⁺ : ∀ x → act-π (rx x) ≡ snd
  cancel⁺ x =
    subst (λ e → act-π e ≡ snd) (centre⁺-rx x) (T⁺ x .center .snd)

  open from-cancel G rx corx using () renaming (absorb⁻ to abs⁻; absorb⁺ to abs⁺)

  absorb⁻ : ∀ {y} (k : coterm y) → coact (corx y) k ≡ k
  absorb⁻ = abs⁻ corx cancel⁻

  absorb⁺ : ∀ {x} (t : term x) → act (rx x) t ≡ t
  absorb⁺ = abs⁺ rx cancel⁺
```

## The far unit laws

One cut per hand, through that hand's action identity.

```agda
module far {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (R : framing.readback-of G rx corx)
  (T⁻ : absorbing⁻.is-absorbing⁻ G rx)
  (T⁺ : absorbing⁺.is-absorbing⁺ G corx) where

  open cancellation G rx corx R T⁻ T⁺ public
  open hand⁺ G rx corx C⁺ R public
  open hand⁻ G rx corx C⁻ R public

  unitl⁺ : ∀ {w x} (s : hom w x) → corx w ⨾⁺ s ≡ s
  unitl⁺ {w} {x} s =
    sym (⨾⁺-is-coact (corx w) s) ∙ happly (cancel⁻ w) (x , s)

  unitr⁻ : ∀ {x v} (k : hom x v) → k ⨾⁻ rx v ≡ k
  unitr⁻ {x} {v} k =
    sym (⨾⁻-is-act k (rx v)) ∙ happly (cancel⁺ v) (x , k)
```

## At contractible cuts

The embedding condition is a theorem here, and `associates` holds
wherever the
units can reach — the word with both trailing edges at the half-twists.

```agda
module at-strength {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (cc⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (framing⁻.composite⁺ G rx f g)))
  (cc⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (framing⁺.composite⁻ G corx f g)))
  (R : framing.readback-of G rx corx)
  (T⁻ : absorbing⁻.is-absorbing⁻ G rx)
  (T⁺ : absorbing⁺.is-absorbing⁺ G corx) where

  C⁺ : framing⁻.is-composable⁺ G rx
  C⁺ f g = cc⁺ f g .center

  C⁻ : framing⁺.is-composable⁻ G corx
  C⁻ f g = cc⁻ f g .center

  open far G rx corx C⁺ C⁻ R T⁻ T⁺ public

  S : reflect-is-embedding G
  S = contr-cut⁻.embedding-from-contr-cut⁻ G rx corx R cc⁻

  open tower G rx corx S C⁺ C⁻ using (associates)

  associates-at-half-twists : ∀ {x y} (f : hom x y)
                       → associates f (corx y) (rx y)
  associates-at-half-twists {x} {y} f =
      ap (_⨾⁻ rx y) (unitr⁺ f)
    ∙ unitr⁻ f
    ∙ sym (ap (f ⨾⁺_) (unitr⁻ (corx y)) ∙ unitr⁺ f)
```

## The polarity collapse

Each hand cuts against the other hand's half-twist; neither pairing is a
unit law. The mixed law moves the pairing's half-twist across the
junction and the hand's own unit law absorbs it, so each cut is the
other cut after its own pairing, and each pairing distributes over
the cut it produces. From there each half-twist condition implies the
other, and the one-edge theorems of `Polarity` send each polarity to
the other one.

```agda
module collapse {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (R : framing.readback-of G rx corx)
  (T⁻ : absorbing⁻.is-absorbing⁻ G rx)
  (T⁺ : absorbing⁺.is-absorbing⁺ G corx) where

  open polarity G rx corx S C⁺ C⁻ public hiding (cut⁻-cross; cut⁺-cross)
  private
    module tw = tower G rx corx S C⁺ C⁻
  open far G rx corx C⁺ C⁻ R T⁻ T⁺ public
    using ( unitl⁺; unitr⁻; unitr⁺; unitl⁻
          ; ⨾⁺-is-coact; ⨾⁻-is-act; composite⁻-half-twist
          ; centre⁻-corx; centre⁺-rx; cancel⁻; cancel⁺
          ; absorb⁻; absorb⁺ )

  pair⁻ : ∀ x → rx x ⨾⁻ corx x ≡ corx x
  pair⁻ x = unitl⁻ (corx x)

  pair⁺ : ∀ x → rx x ⨾⁺ corx x ≡ rx x
  pair⁺ x = unitr⁺ (rx x)

  positive-of-corx : ∀ x → linear (corx x) → positive x
  positive-of-corx x = positive-from-unit x unitl⁺

  negative-of-rx : ∀ x → thunkable (rx x) → negative x
  negative-of-rx x = negative-from-unit x unitr⁻

  cut⁻-cross : ∀ {x y z} (f : hom x y) (g : hom y z)
             → cross⁻ f ⨾⁺ g ≡ f ⨾⁻ g
  cut⁻-cross = tw.cut⁻-cross unitl⁺

  cut⁺-cross : ∀ {x y z} (f : hom x y) (g : hom y z)
             → f ⨾⁻ cross⁺ g ≡ f ⨾⁺ g
  cut⁺-cross = tw.cut⁺-cross unitr⁻

  cross⁻-cut⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → cross⁻ (cross⁻ f ⨾⁺ g) ≡ cross⁻ f ⨾⁺ cross⁻ g
  cross⁻-cut⁺ {z = z} f g =
      ap cross⁻ (cut⁻-cross f g)
    ∙ assoc⁻ f g (corx z)
    ∙ sym (cut⁻-cross f (cross⁻ g))

  cross⁺-cut⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → cross⁺ (f ⨾⁻ cross⁺ g) ≡ cross⁺ f ⨾⁻ cross⁺ g
  cross⁺-cut⁻ {x} f g =
      ap cross⁺ (cut⁺-cross f g)
    ∙ sym (assoc⁺ (rx x) f g)
    ∙ sym (cut⁺-cross (cross⁺ f) g)
```

A linear positive half-twist reads at its own half-twist: the pairing at an
edge into `x` is a positive cut against a fixed edge, the fixed edge
is the pairing at the positive half-twist, and the negative half-twist cuts
onto it as a right inverse. The distribution law then reads at any
edge into `x`.

```agda
  module from-linear {x} (L : linear (corx x)) where
    centre : hom x x
    centre = cross⁻ (corx x)

    cross⁻-into : ∀ {w} (f : hom w x) → cross⁻ f ≡ f ⨾⁺ centre
    cross⁻-into f = ap cross⁻ (sym (unitr⁺ f)) ∙ L f (corx x)

    rx-centre : rx x ⨾⁺ centre ≡ corx x
    rx-centre = sym (cross⁻-into (rx x)) ∙ pair⁻ x

    retract : ∀ {w} (u : hom w x) → cross⁻ (u ⨾⁺ rx x) ≡ u
    retract u =
        cross⁻-into (u ⨾⁺ rx x)
      ∙ assoc⁺ u (rx x) centre
      ∙ ap (u ⨾⁺_) rx-centre
      ∙ unitr⁺ u

    cross⁻-left : ∀ {w y} (u : hom w x) (f : hom x y)
                → cross⁻ (u ⨾⁺ f) ≡ u ⨾⁺ cross⁻ f
    cross⁻-left u f =
        ap (λ e → cross⁻ (e ⨾⁺ f)) (sym (retract u))
      ∙ cross⁻-cut⁺ (u ⨾⁺ rx x) f
      ∙ ap (_⨾⁺ cross⁻ f) (retract u)

    thunkable-rx : thunkable (rx x)
    thunkable-rx g h =
        sym (cut⁻-cross (rx x ⨾⁺ g) h)
      ∙ ap (_⨾⁺ h) (cross⁻-left (rx x) g)
      ∙ assoc⁺ (rx x) (cross⁻ g) h
      ∙ ap (rx x ⨾⁺_) (cut⁻-cross g h)
```

The dual reading takes the pairing at an edge out of `x`, through
the negative cut.

```agda
  module from-thunkable {x} (T : thunkable (rx x)) where
    centre : hom x x
    centre = cross⁺ (rx x)

    cross⁺-out : ∀ {v} (k : hom x v) → cross⁺ k ≡ centre ⨾⁻ k
    cross⁺-out k = ap cross⁺ (sym (unitl⁻ k)) ∙ sym (T (rx x) k)

    centre-corx : centre ⨾⁻ corx x ≡ rx x
    centre-corx = sym (cross⁺-out (corx x)) ∙ pair⁺ x

    retract : ∀ {v} (u : hom x v) → cross⁺ (corx x ⨾⁻ u) ≡ u
    retract u =
        cross⁺-out (corx x ⨾⁻ u)
      ∙ sym (assoc⁻ centre (corx x) u)
      ∙ ap (_⨾⁻ u) centre-corx
      ∙ unitl⁻ u

    cross⁺-right : ∀ {w v} (f : hom w x) (u : hom x v)
                 → cross⁺ (f ⨾⁻ u) ≡ cross⁺ f ⨾⁻ u
    cross⁺-right f u =
        ap (λ e → cross⁺ (f ⨾⁻ e)) (sym (retract u))
      ∙ cross⁺-cut⁻ f (corx x ⨾⁻ u)
      ∙ ap (cross⁺ f ⨾⁻_) (retract u)

    linear-corx : linear (corx x)
    linear-corx f g =
        ap (_⨾⁻ corx x) (sym (cut⁺-cross f g))
      ∙ assoc⁻ f (cross⁺ g) (corx x)
      ∙ ap (f ⨾⁻_) (sym (cross⁺-right g (corx x)))
      ∙ cut⁺-cross f (g ⨾⁻ corx x)
```

```agda
  linear→thunkable : ∀ x → linear (corx x) → thunkable (rx x)
  linear→thunkable _ L = from-linear.thunkable-rx L

  thunkable→linear : ∀ x → thunkable (rx x) → linear (corx x)
  thunkable→linear _ T = from-thunkable.linear-corx T

  positive→negative : ∀ x → positive x → negative x
  positive→negative x P =
    negative-of-rx x (linear→thunkable x (P x (corx x)))

  negative→positive : ∀ x → negative x → positive x
  negative→positive x N =
    positive-of-corx x (thunkable→linear x (N x (rx x)))
```

A distinguishing model would need one object positive and not
negative, or one negative and not positive. Both cases are closed.

```agda
  no-positive-split : ∀ {p} → linear (corx p) → ¬ thunkable (rx p) → ⊥
  no-positive-split L W = W (linear→thunkable _ L)

  no-negative-split : ∀ {n} → thunkable (rx n) → ¬ linear (corx n) → ⊥
  no-negative-split T W = W (thunkable→linear _ T)
```
