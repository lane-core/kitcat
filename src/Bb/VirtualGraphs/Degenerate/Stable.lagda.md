Three statements of the unit tier's coherence, and one theorem that
carries composability, unitality, and the coarsest of the three
across the opposite carrier.

The first statement pins each hand's action at the chosen edge to be
an equivalence, together with that hand's idempotence there. From
those two facts alone — no readback hypothesis anywhere — both
hands' absorption laws follow, and with them a canonical flank for
each hand. A second statement compares the two canonical flanks
against a general readback family, singly for one hand or the other
and jointly for both at once; asking for both at once is strictly
more, since it forces the two flanks to agree. A third statement
drops the canonical flanks altogether: restriction of readback to the
chosen edges is an equivalence outright, and every pinned package —
either canonical flank, or any other family a proof happens to
supply — is one of its fibers. The three live in separate named
scopes (`unital`, again `unital`, and `stable`), so their `is-stable`
names never collide.

Composability, unitality, and the third stability statement each
transport to the opposite carrier along the swap that exchanges term
and coterm. The two equivalence fields of unitality exchange
definitionally; only the two idempotences move, each carried across
by one `ap` of the swap. Composability's transport needs one further
fact — that the swap carries representability to representability —
built once from the swap's own embedding-hood and reused at both
hands.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Stable where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_; is-equiv; iso→equiv; eqv-fibers; is-contr-equiv)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; ×-is-hlevel)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Equiv.Properties using (_∙e_; esym; is-equiv-is-prop)
open import Core.Function.Embedding using (equiv→lc)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing using (module framing)
open import Bb.VirtualGraphs.Embedding
  using (is-representable; opⱽ; swap-judgment; rep-op)
open import Bb.VirtualGraphs.Degenerate.Chosen
```

## Composability and unitality

Composability pairs the two hands' contractibility statements as one
type. Unitality pairs each hand's action-equivalence at the chosen
edge with that hand's idempotence, the idempotence stated at the
judgment rather than at the edge — the datum needs no composition
written down, only the reflected chosen edge equalling its own
composite with itself. Both close over the composite judgments and
actions already built for a chosen edge.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) (open chosen G idn) where

  is-composable : Type (o ⊔ h)
  is-composable =
      (∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable G (composite⁻ f g)))
    × (∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable G (composite⁺ f g)))

  is-unital : Type (o ⊔ h)
  is-unital =
      (∀ {x v} → is-equiv (λ (b : hom x v) → coact-π (idn x) (v , b)))
    × (∀ {w x} → is-equiv (λ (a : hom w x) → act-π (idn x) (w , a)))
    × (∀ x → reflect (idn x) ≡ composite⁻ (idn x) (idn x))
    × (∀ x → reflect (idn x) ≡ composite⁺ (idn x) (idn x))

  is-composable-is-prop : is-prop is-composable
  is-composable-is-prop =
    ×-is-hlevel 1
      (Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
       Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _)
      (Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
       Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _)
```

## The unit tier, emb-action form

Each hand's action at the chosen edge is an equivalence at every far
endpoint, and that hand's composition is idempotent there. Neither
half suffices alone — the equivalences are powerless without the
idempotence, and the idempotence is slack without the equivalences.

```agda
module unital {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) (open chosen G idn)
  (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁻ f g)))
  (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁺ f g)))
  (open composable contr⁻ contr⁺)
  (eqv⁻ : ∀ {x v} → is-equiv (λ (b : hom x v) → coact-π (idn x) (v , b)))
  (eqv⁺ : ∀ {w x} → is-equiv (λ (a : hom w x) → act-π (idn x) (w , a)))
  (rep-idem⁻ : ∀ x → reflect (idn x) ≡ composite⁻ (idn x) (idn x))
  (rep-idem⁺ : ∀ x → reflect (idn x) ≡ composite⁺ (idn x) (idn x))
  where
```

The chosen edge represents its own composite with itself, on each
hand: the fiber's uniqueness turns the reflected-judgment datum above
into an edge-level idempotence.

```agda
  idem⁻ : ∀ x → idn x ⨾⁻ idn x ≡ idn x
  idem⁻ x = ap fst (contr⁻ (idn x) (idn x) .paths (idn x , rep-idem⁻ x))

  idem⁺ : ∀ x → idn x ⨾⁺ idn x ≡ idn x
  idem⁺ x = ap fst (contr⁺ (idn x) (idn x) .paths (idn x , rep-idem⁺ x))
```

Absorption follows by cancelling the equivalence against the
idempotence, over that hand's distributive law. Readback is not in
scope.

```agda
  idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
  idn-absorb⁻ x γ = equiv→lc eqv⁻ step
    where
      step : coact-π (idn x) (γ .fst , coact-π (idn x) γ)
           ≡ coact-π (idn x) (γ .fst , γ .snd)
      step = sym (coact-π-⨾⁻ (idn x) (idn x) γ)
           ∙ ap (λ s → coact-π s γ) (idem⁻ x)

  idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
  idn-absorb⁺ x t = equiv→lc eqv⁺ step
    where
      step : act-π (idn x) (t .fst , act-π (idn x) t)
           ≡ act-π (idn x) (t .fst , t .snd)
      step = sym (act-π-⨾⁺ (idn x) (idn x) t)
           ∙ ap (λ s → act-π s t) (idem⁺ x)
```

Evaluation at the axiom is each action read at its own axiom half, so
each hand's absorption instantiated there is a flank canonical —
constructed, not assumed.

```agda
  canonical-flank⁻ : ∀ x → eval (reflect (idn x)) ≡ idn x
  canonical-flank⁻ x = idn-absorb⁻ x (covar x)

  canonical-flank⁺ : ∀ x → eval (reflect (idn x)) ≡ idn x
  canonical-flank⁺ x = idn-absorb⁺ x (var x)
```

The pin is generic in which canonical it uses, so the same statement
is available for either hand. Asking for both at once is a different
thing: it forces the two canonicals to agree, a path between flank
paths.

```agda
  flank-restrict : framing.readback-of G idn idn
                 → (∀ x → eval (reflect (idn x)) ≡ idn x)
  flank-restrict u x = u (idn x)

  is-stable : Type (o ⊔ h)
  is-stable = is-contr
    (Σ u ∶ framing.readback-of G idn idn
         , (∀ x → u (idn x) ≡ canonical-flank⁻ x))

  is-stable⁺ : Type (o ⊔ h)
  is-stable⁺ = is-contr
    (Σ u ∶ framing.readback-of G idn idn
         , (∀ x → u (idn x) ≡ canonical-flank⁺ x))

  is-stable± : Type (o ⊔ h)
  is-stable± = is-contr
    (Σ u ∶ framing.readback-of G idn idn
         , (∀ x → u (idn x) ≡ canonical-flank⁻ x)
         × (∀ x → u (idn x) ≡ canonical-flank⁺ x))

  both→agree
    : (Σ u ∶ framing.readback-of G idn idn
           , (∀ x → u (idn x) ≡ canonical-flank⁻ x)
           × (∀ x → u (idn x) ≡ canonical-flank⁺ x))
    → ∀ x → canonical-flank⁻ x ≡ canonical-flank⁺ x
  both→agree (u , p , q) x = sym (p x) ∙ q x

  stable±→agree : is-stable± → ∀ x → canonical-flank⁻ x ≡ canonical-flank⁺ x
  stable±→agree S = both→agree (S .center)
```

Taking the two hands as a product of contractibility statements,
rather than one contractibility of a joint package, keeps them
symmetric under the exchange of hands: each factor is separately a
fiber over its own constructed pin.

```agda
  is-stable-pair : Type (o ⊔ h)
  is-stable-pair = is-stable × is-stable⁺
```

## Stability as an equivalence

Restriction to the identities mentions neither hand, nor the unit
tier at all — only `idn` and readback. Asking it to be an
*equivalence* covers every pinned package as one of its fibers, so
both canonical flanks above sit inside a single statement, and the
statement is a proposition because `is-equiv` always is. This is the
third `is-stable` of this file, scoped to its own module and never
opened alongside the other two.

```agda
module stable {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) (open chosen G idn) where

  flank : Type (o ⊔ h)
  flank = ∀ x → eval (reflect (idn x)) ≡ idn x

  restrict : framing.readback-of G idn idn → flank
  restrict u x = u (idn x)

  is-stable : Type (o ⊔ h)
  is-stable = is-equiv restrict

  pinned-contr : is-stable → (t₀ : flank) → is-contr (fiber restrict t₀)
  pinned-contr S t₀ = S .eqv-fibers t₀
```

The codomain is fixed by the graph, so any pin gives a contractible
package this way — in particular either hand's canonical flank above,
with neither privileged and no comparison between them required.

## Composability, transported

Each hand's composability at the opposite is the other hand's here,
read through `rep-op`. The pairing is a proposition, so the round
trip needs no coherence of its own. The two composite judgments agree
with the swap of the other hand's composite definitionally, so the
represented edges agree too, by the fiber's own uniqueness.

```agda
composable-op : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
              (idn : (x : ob) → hom x x)
              → is-composable G idn → is-composable (opⱽ G) idn
composable-op G idn (c⁻ , c⁺) =
    (λ f g → is-contr-equiv (esym (rep-op G _)) (c⁺ g f))
  , (λ f g → is-contr-equiv (esym (rep-op G _)) (c⁻ g f))

composable-op-invol
  : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
    (idn : (x : ob) → hom x x) (C : is-composable G idn)
  → composable-op (opⱽ G) idn (composable-op G idn C) ≡ C
composable-op-invol G idn C = is-composable-is-prop G idn _ _

⨾-op : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
       (idn : (x : ob) → hom x x) (C : is-composable G idn)
       {x y z} (f : hom y x) (g : hom z y)
     → composable-op G idn C .fst f g .center .fst ≡ C .snd g f .center .fst
⨾-op G idn C f g =
  ap fst (composable-op G idn C .fst f g .paths
           (C .snd g f .center .fst
           , ap (swap-judgment G) (C .snd g f .center .snd)))
```

## The unit tier, transported

The two action-equivalences exchange on the nose, since each hand's
action at the opposite is the other hand's action here, definitionally.
Only the two idempotences move, each carried across the swap by one
`ap`. The round trip needs no propositionality argument: the swap is a
definitional involution, so applying it twice returns the starting
idempotence outright.

```agda
unital-op : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
          (idn : (x : ob) → hom x x)
          → is-unital G idn → is-unital (opⱽ G) idn
unital-op G idn (e⁻ , e⁺ , i⁻ , i⁺) =
  e⁺ , e⁻ , (λ x → ap (swap-judgment G) (i⁺ x))
          , (λ x → ap (swap-judgment G) (i⁻ x))

unital-op-invol
  : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
    (idn : (x : ob) → hom x x) (U : is-unital G idn)
  → unital-op (opⱽ G) idn (unital-op G idn U) ≡ U
unital-op-invol G idn U = refl
```

## Opposition

Evaluation at the identities reads both hands' actions, and opposition
exchanges them, so readback restricted to the identities is one type
shared between a carrier and its opposite; the two readback types
themselves differ only by which endpoint of an argument is written
first, an isomorphism with `refl` round trips.

```agda
readback-op : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
            (idn : (x : ob) → hom x x)
            → framing.readback-of (opⱽ G) idn idn
            ≃ framing.readback-of G idn idn
readback-op G idn = iso→equiv (λ u f → u f) (λ u f → u f) (λ _ → refl) (λ _ → refl)

flank-op : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
         (idn : (x : ob) → hom x x)
         → stable.flank (opⱽ G) idn ≡ stable.flank G idn
flank-op G idn = refl

restrict-op
  : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
    (idn : (x : ob) → hom x x) (u : framing.readback-of (opⱽ G) idn idn)
  → stable.restrict (opⱽ G) idn u ≡ stable.restrict G idn (readback-op G idn .fst u)
restrict-op G idn u = refl
```

Stability composes that isomorphism with restriction's own inverse,
and it round-trips for free, being a proposition.

```agda
stable-op : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
          (idn : (x : ob) → hom x x)
          → stable.is-stable G idn → stable.is-stable (opⱽ G) idn
stable-op G idn S = (readback-op G idn ∙e (stable.restrict G idn , S)) .snd

stable-op-invol
  : ∀ {o h} (G : virtual-graph o h) (open virtual-graph G)
    (idn : (x : ob) → hom x x) (S : stable.is-stable G idn)
  → stable-op (opⱽ G) idn (stable-op G idn S) ≡ S
stable-op-invol G idn S = is-equiv-is-prop _ _ _
```
