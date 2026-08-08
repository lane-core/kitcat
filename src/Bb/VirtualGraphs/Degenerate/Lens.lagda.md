The unital layer of the lens. Every construction here runs on the two
absorption tiers and readback, which together pin the fibers' units to
the chosen edge and give each hand its unitor.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Lens where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Path.Base
open import Core.Rx.Type
open import Core.Rx.Base
open import Core.Rx.Properties
open import Core.Rx.Lens
open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Graph using (module two-sided)
open import Bb.VirtualGraphs.Embedding using (is-representable)
open import Bb.VirtualGraphs.Degenerate.Chosen
```

## The vocabulary, axiom-free

Holding one slot of an argument at its axiom half leaves an
injection: the coterm slot open gives `inj⁻`, the term slot open
`inj⁺`. They are the framing's injections at the diagonal, crossed
the way the composites are.

```agda
module lens {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn
  open dict G idn using (graph)

  inj⁻ : ∀ {x y z} → judgment x y → hom y z → judgment x z
  inj⁻ = framing⁻.inj⁺ G idn

  inj⁺ : ∀ {x y z} → hom x y → judgment y z → judgment x z
  inj⁺ = framing⁺.inj⁻ G idn

  judgment± : rx.efam graph (o ⊔ h) (o ⊔ h)
  judgment± x y _ = discrete (judgment x y)

  hom± : rx.efam graph h h
  hom± x y _ = discrete (hom x y)
```

Paired with its own opposite, `graph` carries the judgment family in
one covariant move. `Graph` builds that base over a framing, and this
is its diagonal.

```agda
  two-sided : reflexive-graph o h
  two-sided = two-sided.base G idn idn

  bipush : ∀ {x y x' y'} → hom x' x → hom y y' → judgment x y → judgment x' y'
  bipush = two-sided.bipush G idn idn

  judgment-fam : rx.vfam two-sided (o ⊔ h) (o ⊔ h)
  judgment-fam = two-sided.judgment-fam G idn idn

  interchange : Type (o ⊔ h)
  interchange = ∀ {x y z} (f : hom x y) (g : hom y z)
              → composite⁻ f g ≡ composite⁺ f g
```

## The judgment lens

A lens states its unitors at the base's own reflexive edge, `idn`.
Absorption holds at the units the fibers project, and readback bridges
those units to `idn` itself.

```agda
module unital {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x)
  (open chosen G idn) (open dict G idn using (graph)) (open lens G idn)
  (unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
  (unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd))
  (rb : framing.readback-of G idn idn)
  where

  unit⁻ unit⁺ : ∀ x → hom x x
  unit⁻ x = unit-fiber⁻ x .center .fst
  unit⁺ x = unit-fiber⁺ x .center .fst

  unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
  unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

  unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
  unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t

  unit⁻-is-idn : ∀ x → unit⁻ x ≡ idn x
  unit⁻-is-idn x = sym (rb (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

  unit⁺-is-idn : ∀ x → unit⁺ x ≡ idn x
  unit⁺-is-idn x = sym (rb (unit⁺ x)) ∙ unit⁺-absorb x (var x)

  idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
  idn-absorb⁻ x γ =
    ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ

  idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
  idn-absorb⁺ x t =
    ap (λ e → act-π e t) (sym (unit⁺-is-idn x)) ∙ unit⁺-absorb x t
```

Each unitor is one absorption read under a judgment, at whichever
slot that hand consumes.

```agda
  absorb⁻ : ∀ {x} (α : judgment x x) → inj⁻ α (idn x) ≡ α
  absorb⁻ {x} α = funext λ γ →
    ap (λ b → α (argue (γ .fst) (γ .snd .fst , b))) (idn-absorb⁻ x (γ .snd))

  absorb⁺ : ∀ {x} (α : judgment x x) → inj⁺ (idn x) α ≡ α
  absorb⁺ {x} α = funext λ γ →
    ap (λ a → α (argue (γ .fst .fst , a) (γ .snd))) (idn-absorb⁺ x (γ .fst))

  judgment-lens : unbiased-lens graph judgment±
  judgment-lens .unbiased-lens.linj    _ _ p α = inj⁻ α p
  judgment-lens .unbiased-lens.rinj    _ _ p β = inj⁺ p β
  judgment-lens .unbiased-lens.munitor _   α   = absorb⁻ α ∙ sym (absorb⁺ α)
  judgment-lens .unbiased-lens.runitor _   α   = sym (absorb⁺ α)

  judgment-disp : rx.disp graph (o ⊔ h) (o ⊔ h)
  judgment-disp = unbiased-lens.display judgment-lens

  judgment-disp-path-object : is-displayed-univalent judgment-disp
  judgment-disp-path-object =
    unb-disp-path-object judgment-lens (λ _ → disc-path-object _)
```

## The mid unitor against the flank coherence

The mid unitor compares the two injections on an endo-judgment at
`idn`. The flank coherence compares two derivations of a path in a
hom type — one dimension up. An unbiased lens' unitors are edges of
a discrete component, so they reach no higher.

```agda
  munitor-at-rx : ∀ x (α : judgment x x) → inj⁻ α (idn x) ≡ inj⁺ (idn x) α
  munitor-at-rx = unbiased-lens.munitor judgment-lens

  flank⁻-of : ∀ x → eval (reflect (unit⁻ x)) ≡ unit⁻ x
            → eval (reflect (idn x)) ≡ idn x
  flank⁻-of x p =
    ap (λ e → coact-π e (covar x)) (sym (sym p ∙ unit⁻-absorb x (covar x)))
    ∙ unit⁻-absorb x (covar x)

  flank⁺-of : ∀ x → eval (reflect (unit⁺ x)) ≡ unit⁺ x
            → eval (reflect (idn x)) ≡ idn x
  flank⁺-of x p =
    ap (λ e → act-π e (var x)) (sym (sym p ∙ unit⁺-absorb x (var x)))
    ∙ unit⁺-absorb x (var x)

  flanks-agree : Type (o ⊔ h)
  flanks-agree = ∀ x → flank⁻-of x (rb (unit⁻ x)) ≡ flank⁺-of x (rb (unit⁺ x))
```

## The two-sided lens

The same two hypotheses give the two-sided base its own lens:
`bipush` at reflexivity on both legs is the identity, since each
action's absorption is exactly `idn-absorb⁻`/`idn-absorb⁺`.

```agda
  coact-idn : ∀ {y} (e : coterm y) → coact (idn y) e ≡ e
  coact-idn {y} e i = e .fst , idn-absorb⁻ y e i

  act-idn : ∀ {x} (t : term x) → act (idn x) t ≡ t
  act-idn {x} t i = t .fst , idn-absorb⁺ x t i

  bipush-idn : ∀ {x y} (α : judgment x y) → bipush (idn x) (idn y) α ≡ α
  bipush-idn α = funext λ γ → λ i →
    α (argue (act-idn (γ .fst) i) (coact-idn (γ .snd) i))

  two-sided-lens : oplax-cov-lens two-sided judgment-fam
  two-sided-lens .oplax-cov-lens.has-push _ _ (a , b) = bipush a b
  two-sided-lens .oplax-cov-lens.has-unitor = bipush-idn

  two-sided-disp : rx.disp two-sided (o ⊔ h) (o ⊔ h)
  two-sided-disp = oplax-cov-lens.display two-sided-lens

  two-sided-disp-path-object : is-displayed-univalent two-sided-disp
  two-sided-disp-path-object =
    cov-disp-path-object two-sided-lens (λ _ → disc-path-object _)
```

Each composite judgment is the two-sided action with one leg held at
`idn`, applied to one factor's reflection. The two land in the fiber
at the outer pair from different vertices — a cospan — and
interchange is exactly its agreement.

```agda
  push-is-composite⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
                     → bipush (idn x) g (reflect f) ≡ composite⁻ f g
  push-is-composite⁻ f g = funext λ γ → λ i →
    reflect f (argue (act-idn (γ .fst) i) (coact g (γ .snd)))

  push-is-composite⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
                     → bipush f (idn z) (reflect g) ≡ composite⁺ f g
  push-is-composite⁺ f g = funext λ γ → λ i →
    reflect g (argue (act f (γ .fst)) (coact-idn (γ .snd) i))

  interchange-is-cospan
    : interchange
    → ∀ {x y z} (f : hom x y) (g : hom y z)
    → bipush (idn x) g (reflect f) ≡ bipush f (idn z) (reflect g)
  interchange-is-cospan I f g =
    push-is-composite⁻ f g ∙ I f g ∙ sym (push-is-composite⁺ f g)

  cospan-is-interchange
    : (∀ {x y z} (f : hom x y) (g : hom y z)
       → bipush (idn x) g (reflect f) ≡ bipush f (idn z) (reflect g))
    → interchange
  cospan-is-interchange C f g =
    sym (push-is-composite⁻ f g) ∙ C f g ∙ push-is-composite⁺ f g
```

## The hom lens, and composites agree

Composability's two compositions are the hom family's own lens
injections, with the two unit laws readback supplies as unitors. The
two-sided action distributes over each hand's own composition, but
lands on a base edge mixing `⁺` on one leg and `⁻` on the other, so
a lens alone is never functorial. `composites-agree` is exactly the
missing piece, and interchange delivers it.

```agda
  module _
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁻ f g)))
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
              → is-contr (is-representable G (composite⁺ f g)))
    where

    open composable contr⁻ contr⁺

    composite⁻-unitr : ∀ {a y} (u : hom a y) → reflect u ≡ composite⁻ u (idn y)
    composite⁻-unitr u = funext λ γ →
      ap (λ e → reflect u (argue (γ .fst) e)) (sym (coact-idn (γ .snd)))

    composite⁺-unitl : ∀ {x c} (u : hom x c) → reflect u ≡ composite⁺ (idn x) u
    composite⁺-unitl u = funext λ γ →
      ap (λ t → reflect u (argue t (γ .snd))) (sym (act-idn (γ .fst)))

    unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ idn y ≡ f
    unitr⁻ {y = y} f =
      sym (rb (f ⨾⁻ idn y))
      ∙ ap eval (reflect-⨾⁻ f (idn y) ∙ sym (composite⁻-unitr f))
      ∙ rb f

    unitl⁺ : ∀ {x y} (f : hom x y) → idn x ⨾⁺ f ≡ f
    unitl⁺ {x} f =
      sym (rb (idn x ⨾⁺ f))
      ∙ ap eval (reflect-⨾⁺ (idn x) f ∙ sym (composite⁺-unitl f))
      ∙ rb f

    hom-lens : unbiased-lens graph hom±
    hom-lens .unbiased-lens.linj    _ _ p e = e ⨾⁻ p
    hom-lens .unbiased-lens.rinj    _ _ p e = p ⨾⁺ e
    hom-lens .unbiased-lens.munitor _   e   = unitr⁻ e ∙ sym (unitl⁺ e)
    hom-lens .unbiased-lens.runitor _   e   = sym (unitl⁺ e)

    hom-disp : rx.disp graph h h
    hom-disp = unbiased-lens.display hom-lens

    hom-disp-path-object : is-displayed-univalent hom-disp
    hom-disp-path-object =
      unb-disp-path-object hom-lens (λ _ → disc-path-object _)

    reflect-disp-edge
      : ∀ {x y} (p : hom x y) (d : hom x x) (e : hom y y)
      → d ⨾⁻ p ≡ p ⨾⁺ e
      → inj⁻ (reflect d) p ≡ inj⁺ p (reflect e)
    reflect-disp-edge p d e q =
      sym (reflect-⨾⁻ d p) ∙ ap reflect q ∙ reflect-⨾⁺ p e

    bipush-comp
      : ∀ {x y x' y' x'' y''}
        (a : hom x' x) (a' : hom x'' x') (b : hom y y') (b' : hom y' y'')
        (α : judgment x y)
      → bipush a' b' (bipush a b α) ≡ bipush (a' ⨾⁺ a) (b ⨾⁻ b') α
    bipush-comp a a' b b' α = funext λ γ → λ i →
      α (argue (act-⨾⁺ a' a (γ .fst) (~ i)) (coact-⨾⁻ b b' (γ .snd) (~ i)))

    composites-agree : Type (o ⊔ h)
    composites-agree = ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ⨾⁺ g

    bipush-comp-mediated
      : composites-agree
      → ∀ {x y x' y' x'' y''}
        (a : hom x' x) (a' : hom x'' x') (b : hom y y') (b' : hom y' y'')
        (α : judgment x y)
      → bipush a' b' (bipush a b α) ≡ bipush (a' ⨾⁻ a) (b ⨾⁻ b') α
    bipush-comp-mediated M a a' b b' α =
      bipush-comp a a' b b' α
      ∙ ap (λ c → bipush c (b ⨾⁻ b') α) (sym (M a' a))

    interchange→composites-agree : interchange → composites-agree
    interchange→composites-agree I f g =
      sym (rb (f ⨾⁻ g))
      ∙ ap eval (reflect-⨾⁻ f g ∙ I f g ∙ sym (reflect-⨾⁺ f g))
      ∙ rb (f ⨾⁺ g)
```

## What the lens does not carry

Both unitor shapes are available on the judgment lens. `absorb⁻` is
the oplax one — injecting on the left at reflexivity is the identity
— and `absorb⁺` the lax one `runitor` records. Sterling admits
either but warns against a lens carrying both, on pain of losing
propositionality of the structure over a path-object base
(`resources/sterling-reflexive-graph-lenses`, `paper.tex:2203`;
SOURCE-CHECKED), and draws the same analogy with half-adjoint
equivalences that `Bb.VirtualGraphs.Degenerate.Chosen`'s
`half-adjoint-forces-truncation` makes concrete for readback. This
family carries both, so no propositionality is claimed for it — a
base that is not a path object had already put it out of reach.

What does transfer is univalence of the display. `unb-disp-path-object`
and `cov-disp-path-object` need path objects of the diagonal
components only, never of the base, and the components above are
discrete, so every display here is univalent outright.

Mixed variance is a fact about the base, not about `judgment`.
Displayed over the objects, `judgment` needs the unbiased lens and
its two injections; displayed over the objects paired with their
opposite, it is an ordinary covariant lens with one transport and
one unitor. Interchange is that second lens' missing functoriality:
`bipush` composes from composability alone, but the composite base
edge it lands on carries `⁺` on the backward leg and `⁻` on the
forward one, and only `composites-agree` makes those one operation.
