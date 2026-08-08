Two hypotheses over the readback tower: each far flanking operation
is an equivalence of edge types. Readback makes the two near flanks
the identity already, so the hypotheses constrain the far side alone.
Each far flank is idempotent, an idempotent equivalence is the
identity, and the two far unit laws follow — with them each half-twist
commutes past every edge of its own hand, both cancellations hold,
both absorptions hold, and the polarity collapse runs. Ahead of the
tower, readback alone reads the absorption fibers: every point of one
is the half-twist of the other sign.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Neutral where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (_≃_; is-equiv; id-equiv)
open import Core.Function.Embedding
  using (equiv→lc; is-equiv→is-embedding; is-embedding→ap-equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Degenerate.Readback
open import Bb.VirtualGraphs.Degenerate.Cancellation
```

## The crossing

An absorption fiber holds an edge whose action is the second
projection. Readback names that edge. Read the fiber's own equation
at the axiom half the fiber leaves open: the left side reflects the
edge at its own axiom, which readback returns, and the right side is
the half-twist of the other sign. So each point of the negative fiber is
`corx`, each point of the positive fiber is `rx`, and each point's
equation transports to its half-twist. The argument reads readback and one
fiber point. No cut, no embedding condition, and no contractibility
enters it.

`Cancellation`'s `centre⁻-corx`, `centre⁺-rx`, `cancel⁻`, and
`cancel⁺` are these four statements read at the centre of an
absorption tier.

```agda
module crossing {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (R : framing.readback-of G rx corx) where

  open framing G rx corx

  fiber⁻-corx : (x : ob) (w : fiber (coact-π {x} {x}) snd)
              → w .fst ≡ corx x
  fiber⁻-corx x (e , p) = sym (R e) ∙ happly p (covar x)

  fiber⁺-rx : (x : ob) (w : fiber (act-π {x} {x}) snd)
            → w .fst ≡ rx x
  fiber⁺-rx x (e , p) = sym (R e) ∙ happly p (var x)

  cancel⁻ : (x : ob) → fiber (coact-π {x} {x}) snd → coact-π (corx x) ≡ snd
  cancel⁻ x w = subst (λ e → coact-π e ≡ snd) (fiber⁻-corx x w) (w .snd)

  cancel⁺ : (x : ob) → fiber (act-π {x} {x}) snd → act-π (rx x) ≡ snd
  cancel⁺ x w = subst (λ e → act-π e ≡ snd) (fiber⁺-rx x w) (w .snd)
```

## The far flanks

The module head carries the whole hypothesis: the tower, readback,
and one flank equivalence per hand. Each far flank is idempotent —
the flank cuts its half-twist on twice, associativity collects the two
copies, and the near unit law of that hand contracts them to one.

```agda
module neutral {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (R : framing.readback-of G rx corx)
  (N⁻ : ∀ {x y} → is-equiv (tower.flanks.P' G rx corx S C⁺ C⁻ {x} {y}))
  (N⁺ : ∀ {x y} → is-equiv (tower.flanks.Q' G rx corx S C⁺ C⁻ {x} {y})) where

  open readback-tower G rx corx S C⁺ C⁻ R public
    hiding (cut⁻-cross; cut⁺-cross)
  private
    module tw = tower G rx corx S C⁺ C⁻

  idem⁻ : ∀ {x y} (n : hom x y) → flanks.P' (flanks.P' n) ≡ flanks.P' n
  idem⁻ {y = y} n =
    assoc⁻ n (rx y) (rx y) ∙ ap (n ⨾⁻_) (unitl⁻ (rx y))

  idem⁺ : ∀ {x y} (m : hom x y) → flanks.Q' (flanks.Q' m) ≡ flanks.Q' m
  idem⁺ {x} m =
    sym (assoc⁺ (corx x) (corx x) m) ∙ ap (_⨾⁺ m) (unitr⁺ (corx x))
```

A flank that is an equivalence is an embedding, so `ap` of it is an
equivalence of path spaces: the far unit law at an edge on the left,
idempotence at that edge on the right. Both sides are path types, and
the equivalence moves the statement without lowering the h-level of
either side. The direction it supplies runs from idempotence back to
the unit law, and idempotence is a theorem, so each far unit law is
one.

```agda
  unitr⁻≃idem⁻
    : ∀ {x y} (n : hom x y)
    → (flanks.P' n ≡ n) ≃ (flanks.P' (flanks.P' n) ≡ flanks.P' n)
  unitr⁻≃idem⁻ {x} {y} n =
      ap (flanks.P' {x} {y})
    , is-embedding→ap-equiv (is-equiv→is-embedding (N⁻ {x} {y}))

  unitl⁺≃idem⁺
    : ∀ {x y} (m : hom x y)
    → (flanks.Q' m ≡ m) ≃ (flanks.Q' (flanks.Q' m) ≡ flanks.Q' m)
  unitl⁺≃idem⁺ {x} {y} m =
      ap (flanks.Q' {x} {y})
    , is-embedding→ap-equiv (is-equiv→is-embedding (N⁺ {x} {y}))

  unitr⁻ : unitr⁻-law
  unitr⁻ {x} {y} n = equiv→lc (N⁻ {x} {y}) (idem⁻ n)

  unitl⁺ : unitl⁺-law
  unitl⁺ {x} {y} m = equiv→lc (N⁺ {x} {y}) (idem⁺ m)
```

Each half-twist is now a two-sided unit of its own hand, so it commutes
past every edge of that hand. The cut is the hand's action read at
the axiom, so each far unit law is also a cancellation, and the
absorptions follow.

```agda
  natural⁻ : nat⁻-law
  natural⁻ m = unitl⁻ m ∙ sym (unitr⁻ m)

  natural⁺ : nat⁺-law
  natural⁺ m = unitl⁺ m ∙ sym (unitr⁺ m)

  cancel⁻ : ∀ x → coact-π (corx x) ≡ snd
  cancel⁻ x = funext λ γ → ⨾⁺-is-coact (corx x) (γ .snd) ∙ unitl⁺ (γ .snd)

  cancel⁺ : ∀ x → act-π (rx x) ≡ snd
  cancel⁺ x = funext λ t → ⨾⁻-is-act (t .snd) (rx x) ∙ unitr⁻ (t .snd)

  open from-cancel G rx corx using () renaming (absorb⁻ to abs⁻; absorb⁺ to abs⁺)

  absorb⁻ : ∀ {y} (k : coterm y) → coact (corx y) k ≡ k
  absorb⁻ = abs⁻ corx cancel⁻

  absorb⁺ : ∀ {x} (t : term x) → act (rx x) t ≡ t
  absorb⁺ = abs⁺ rx cancel⁺
```

## The polarity collapse

Each hand cuts against the other hand's half-twist; neither pairing is a
unit law. The mixed law moves the pairing's half-twist across the junction
and the hand's own far unit law absorbs it, so each cut is the other
cut after its own pairing, and each pairing distributes over the cut
it produces.

`Cancellation`'s `collapse` proves the same laws and the same two
implications below from readback together with the two absorption
tiers. The hypotheses here are readback together with the two flank
equivalences.

```agda
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

The dual reading takes the pairing at an edge out of `x`, through the
negative cut.

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
```

## The hypotheses from the absorption tiers

The absorption tiers reach both far unit laws over readback, and a
flank equal to the identity is an equivalence. So a carrier meeting
the hypotheses of `Cancellation`'s `far` meets the two hypotheses
above.

```agda
module from-absorbing {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (R : framing.readback-of G rx corx)
  (T⁻ : absorbing⁻.is-absorbing⁻ G rx)
  (T⁺ : absorbing⁺.is-absorbing⁺ G corx) where

  open readback-tower G rx corx S C⁺ C⁻ R public
  open far G rx corx C⁺ C⁻ R T⁻ T⁺ using (unitr⁻; unitl⁺)

  N⁻ : ∀ {x y} → is-equiv (tower.flanks.P' G rx corx S C⁺ C⁻ {x} {y})
  N⁻ {x} {y} = subst is-equiv (sym (funext (unitr⁻ {x} {y}))) id-equiv

  N⁺ : ∀ {x y} → is-equiv (tower.flanks.Q' G rx corx S C⁺ C⁻ {x} {y})
  N⁺ {x} {y} = subst is-equiv (sym (funext (unitl⁺ {x} {y}))) id-equiv
```
