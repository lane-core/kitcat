The chosen edge `idn` carries its own two absorptions as hypotheses,
`absorb⁻` and `absorb⁺`, rather than standing in a relation to the
unit tier only through a separate fiber. Given also that each hand's
unit fiber is contractible, `idn`'s own absorption identifies it with
the fiber's centre directly, with no separate step needed to show it
canonical. `redundancy` drops the fiber hypothesis entirely: stated
as an equivalence, stability alone turns the carrier's own absorption
into a full readback family, and every absorbing edge equals `idn` by
that readback.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Reflexive where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Equiv.Base using (is-equiv; eqv-fibers)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing using (module framing)
open import Bb.VirtualGraphs.Degenerate.Chosen
open import Bb.VirtualGraphs.Embedding using (opⱽ)
```

## The absorbing edge

`absorb⁻` and `absorb⁺` say that `idn` already acts as the identity
action on each hand — not merely that some edge does, but that this
particular family does, at every object.

Opposing the graph exchanges terms and coterms, and with them the two
hands' actions, definitionally (`Engine`'s own involution section
states the same exchange for `act`/`coact`). At the diagonal `idn`,
the same computation identifies `act-π`/`coact-π` for the opposite
graph with `coact-π`/`act-π` for the graph itself, so each absorption
for `opⱽ G` is, on the nose, the other absorption for `G` — no new
proof term, only the swap of which hypothesis discharges which
obligation.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) (open chosen G idn)
  (absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd)
  (absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd)
  where

  private
    module Lᵒ = chosen (opⱽ G) idn

  absorb⁻-op : ∀ x (γ : virtual-graph.coterm (opⱽ G) x)
             → Lᵒ.coact-π (idn x) γ ≡ γ .snd
  absorb⁻-op = absorb⁺

  absorb⁺-op : ∀ x (t : virtual-graph.term (opⱽ G) x)
             → Lᵒ.act-π (idn x) t ≡ t .snd
  absorb⁺-op = absorb⁻
```

## The chosen edge is the unit

Add each hand's unit-fiber hypothesis, the same hypothesis `Engine`'s
own unit tier takes, unrelated to `idn` by itself. Feeding `idn` and
its own absorption into the fiber's contraction identifies `idn` with
the fiber's centre directly: `idn` is not merely an absorbing edge
that a further argument must show canonical, it already inhabits the
fiber. Uniqueness of the absorbing edge follows the same way — any
edge on the fiber over the same point is that centre, hence `idn`.

```agda
  module _ (unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
           (unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd))
           where

    unit⁻ unit⁺ : ∀ x → hom x x
    unit⁻ x = unit-fiber⁻ x .center .fst
    unit⁺ x = unit-fiber⁺ x .center .fst

    idn-is-unit⁻ : ∀ x → unit⁻ x ≡ idn x
    idn-is-unit⁻ x = ap fst (unit-fiber⁻ x .paths (idn x , funext (absorb⁻ x)))

    idn-is-unit⁺ : ∀ x → unit⁺ x ≡ idn x
    idn-is-unit⁺ x = ap fst (unit-fiber⁺ x .paths (idn x , funext (absorb⁺ x)))

    units-agree : ∀ x → unit⁻ x ≡ unit⁺ x
    units-agree x = idn-is-unit⁻ x ∙ sym (idn-is-unit⁺ x)

    unit⁻-unique : ∀ x (e : hom x x) → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
    unit⁻-unique x e p =
      sym (ap fst (unit-fiber⁻ x .paths (e , funext p))) ∙ idn-is-unit⁻ x

    unit⁺-unique : ∀ x (e : hom x x) → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
    unit⁺-unique x e p =
      sym (ap fst (unit-fiber⁺ x .paths (e , funext p))) ∙ idn-is-unit⁺ x
```

## Redundancy

`redundancy` drops the unit-fiber hypotheses entirely. `readback`
supplies every edge from its own reflection; `flank` is that
statement at `idn` alone; `restrict` is a readback family cut down
to its value at each `idn`. Stability names an equivalence at
`restrict`.

The carrier's own absorption at `idn`'s axiom half is already a
`flank` point, so the equivalence hands back a full readback family
with no unit fiber in sight, and every edge absorbing on either hand
equals `idn` by that readback alone.

```agda
  flank : Type (o ⊔ h)
  flank = ∀ x → eval (reflect (idn x)) ≡ idn x

  restrict : framing.readback-of G idn idn → flank
  restrict u x = u (idn x)

  module redundancy (S : is-equiv restrict) where

    flank-pt : flank
    flank-pt x = absorb⁻ x (covar x)

    rb : framing.readback-of G idn idn
    rb = S .eqv-fibers flank-pt .center .fst

    absorber-is-idn⁻ : ∀ x (e : hom x x) → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
    absorber-is-idn⁻ x e p = sym (rb e) ∙ p (covar x)

    absorber-is-idn⁺ : ∀ x (e : hom x x) → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
    absorber-is-idn⁺ x e p = sym (rb e) ∙ p (var x)
```
