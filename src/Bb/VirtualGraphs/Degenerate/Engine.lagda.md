The unit tier over the chosen-edge engine. Everything here runs on the
two tiers: each fiber centre is an edge whose action is the identity
action, and that is the only property the arguments use.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Engine where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (subst; J)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding
open import Core.Rx.Type
open import Core.Rx.Base
open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing using (module framing)
open import Bb.VirtualGraphs.Embedding using (is-representable; normal; opⱽ)
open import Bb.VirtualGraphs.Graph using (rxgraph; op-rxgraph)
open import Bb.VirtualGraphs.Degenerate.Chosen
```

## The engine

The chosen edge plays no part below. Everything runs on the unit
tier's own projected units — the tier's fiber centre is an edge
whose action is the identity action, which is the only property the
argument uses. `idn` is needed to state the vocabulary, and no
result here asks it to be a unit.

```agda
module engine {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x)
  (open chosen G idn)
  (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
          → is-contr (is-representable G (composite⁻ f g)))
  (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
          → is-contr (is-representable G (composite⁺ f g)))
  (open chosen.composable G idn contr⁻ contr⁺)
  (unit-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
  (unit-fiber⁺ : ∀ x → is-contr (fiber (act-π   {x} {x}) snd))
  where

  unit⁻ unit⁺ : ∀ x → hom x x
  unit⁻ x = unit-fiber⁻ x .center .fst
  unit⁺ x = unit-fiber⁺ x .center .fst

  unit⁻-absorb : ∀ x (γ : coterm x) → coact-π (unit⁻ x) γ ≡ γ .snd
  unit⁻-absorb x γ i = unit-fiber⁻ x .center .snd i γ

  unit⁺-absorb : ∀ x (t : term x) → act-π (unit⁺ x) t ≡ t .snd
  unit⁺-absorb x t i = unit-fiber⁺ x .center .snd i t

  unit⁻-unique : ∀ x (e : hom x x)
               → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ unit⁻ x
  unit⁻-unique x e abs = ap fst (sym (unit-fiber⁻ x .paths (e , funext abs)))

  unit⁺-unique : ∀ x (e : hom x x)
               → (∀ t → act-π e t ≡ t .snd) → e ≡ unit⁺ x
  unit⁺-unique x e abs = ap fst (sym (unit-fiber⁺ x .paths (e , funext abs)))

  coact-unit : ∀ {y} (e : coterm y) → coact (unit⁻ y) e ≡ e
  coact-unit {y} e i = e .fst , unit⁻-absorb y e i

  act-unit : ∀ {x} (t : term x) → act (unit⁺ x) t ≡ t
  act-unit {x} t i = t .fst , unit⁺-absorb x t i

  composite⁻-unitr : ∀ {a y} (u : hom a y) → reflect u ≡ composite⁻ u (unit⁻ y)
  composite⁻-unitr u i γ = reflect u (argue (γ .fst) (coact-unit (γ .snd) (~ i)))

  composite⁺-unitl : ∀ {x c} (u : hom x c) → reflect u ≡ composite⁺ (unit⁺ x) u
  composite⁺-unitl u i γ = reflect u (argue (act-unit (γ .fst) (~ i)) (γ .snd))
```

A reflected edge is its own hand's composite with the projected
unit, so the composability fiber over that composite is the fiber
over the reflection: each hand delivers the same contractibility,
and with it left-cancellability, embedding-hood, and the iterated
`ap`-equivalence.

```agda
  reflect-fiber-contr⁻
    : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
  reflect-fiber-contr⁻ {y = y} f =
    subst (λ α → is-contr (is-representable G α))
          (sym (composite⁻-unitr f)) (contr⁻ f (unit⁻ y))

  reflect-fiber-contr⁺
    : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
  reflect-fiber-contr⁺ {x} f =
    subst (λ α → is-contr (is-representable G α))
          (sym (composite⁺-unitl f)) (contr⁺ (unit⁺ x) f)

  reflect-lc : ∀ {x y} {f g : hom x y} → reflect f ≡ reflect g → f ≡ g
  reflect-lc {y = y} {f} {g} p =
    ap fst (sym (c .paths (f , p)) ∙ c .paths (normal G g))
    where c = reflect-fiber-contr⁻ g

  reflect-embedding : ∀ {x y} → is-embedding (reflect {x} {y})
  reflect-embedding α c@(f , p) =
    subst (λ β → is-prop (is-representable G β)) p
          (is-contr→is-prop (reflect-fiber-contr⁻ f)) c

  ap-reflect-equiv
    : ∀ {x y} {f g : hom x y} → is-equiv (ap (reflect {x} {y}) {f} {g})
  ap-reflect-equiv = is-embedding→ap-equiv reflect-embedding

  ap-reflect-embedding
    : ∀ {x y} {f g : hom x y} → is-embedding (ap (reflect {x} {y}) {f} {g})
  ap-reflect-embedding = ap-is-embedding reflect-embedding
```

Associativity and the unit laws come per hand: both bracketings
represent one judgment, by the outer head's rewriting followed by
that hand's distributive law, and left-cancellation descends the
identity from judgments to edges. Readback is not among the inputs.

```agda
  composite⁻-assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
    → composite⁻ (f ⨾⁻ g) h ≡ composite⁻ f (g ⨾⁻ h)
  composite⁻-assoc f g h = funext λ γ →
    (λ i → reflect-⨾⁻ f g i (argue (γ .fst) (coact h (γ .snd))))
    ∙ (λ i → reflect f (argue (γ .fst) (coact-⨾⁻ g h (γ .snd) (~ i))))

  assoc⁻ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
         → (f ⨾⁻ g) ⨾⁻ h ≡ f ⨾⁻ (g ⨾⁻ h)
  assoc⁻ f g h = reflect-lc
    ( reflect-⨾⁻ (f ⨾⁻ g) h
    ∙ composite⁻-assoc f g h
    ∙ sym (reflect-⨾⁻ f (g ⨾⁻ h)) )

  composite⁺-assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
    → composite⁺ f (g ⨾⁺ h) ≡ composite⁺ (f ⨾⁺ g) h
  composite⁺-assoc f g h = funext λ γ →
    (λ i → reflect-⨾⁺ g h i (argue (act f (γ .fst)) (γ .snd)))
    ∙ (λ i → reflect h (argue (act-⨾⁺ f g (γ .fst) (~ i)) (γ .snd)))

  assoc⁺ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
         → f ⨾⁺ (g ⨾⁺ h) ≡ (f ⨾⁺ g) ⨾⁺ h
  assoc⁺ f g h = reflect-lc
    ( reflect-⨾⁺ f (g ⨾⁺ h)
    ∙ composite⁺-assoc f g h
    ∙ sym (reflect-⨾⁺ (f ⨾⁺ g) h) )

  unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ unit⁻ y ≡ f
  unitr⁻ {y = y} f =
    reflect-lc (reflect-⨾⁻ f (unit⁻ y) ∙ sym (composite⁻-unitr f))

  unitl⁺ : ∀ {x y} (f : hom x y) → unit⁺ x ⨾⁺ f ≡ f
  unitl⁺ {x} f =
    reflect-lc (reflect-⨾⁺ (unit⁺ x) f ∙ sym (composite⁺-unitl f))
```

## Stability

A third tier rests on one hypothesis, `rb`. It gives a path for every
edge, identifying that edge with the evaluation of its own
reflection. Composability plays no part below. The unit tier lends
only its two projected units and their absorptions.

The tier does not need the unit tier's own contractibility.
Evaluation at either hand's axiom is that hand's action applied to
its own fiber point. Both facts hold by `refl`.

```agda
  module stability (rb : ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f) where

    eval-is-coact : ∀ {x} (e : hom x x) → eval (reflect e) ≡ coact-π e (covar x)
    eval-is-coact _ = refl

    eval-is-act : ∀ {x} (e : hom x x) → eval (reflect e) ≡ act-π e (var x)
    eval-is-act _ = refl
```

Compose a projected unit's absorption at its own axiom with `rb` at
that unit. The composite identifies the unit with `idn`. Each hand's
absorption then transports onto the chosen edge. The two hands'
units coincide. The same composite identifies any edge whose action
is the identity action with `idn` directly. It needs no detour
through a projected unit.

```agda
    unit⁻-is-idn : ∀ x → unit⁻ x ≡ idn x
    unit⁻-is-idn x = sym (rb (unit⁻ x)) ∙ unit⁻-absorb x (covar x)

    unit⁺-is-idn : ∀ x → unit⁺ x ≡ idn x
    unit⁺-is-idn x = sym (rb (unit⁺ x)) ∙ unit⁺-absorb x (var x)

    units-agree : ∀ x → unit⁻ x ≡ unit⁺ x
    units-agree x = unit⁻-is-idn x ∙ sym (unit⁺-is-idn x)

    idn-absorb⁻ : ∀ x (γ : coterm x) → coact-π (idn x) γ ≡ γ .snd
    idn-absorb⁻ x γ =
      ap (λ e → coact-π e γ) (sym (unit⁻-is-idn x)) ∙ unit⁻-absorb x γ

    idn-absorb⁺ : ∀ x (t : term x) → act-π (idn x) t ≡ t .snd
    idn-absorb⁺ x t =
      ap (λ e → act-π e t) (sym (unit⁺-is-idn x)) ∙ unit⁺-absorb x t

    unit⁻-canonical : ∀ x (e : hom x x)
                    → (∀ γ → coact-π e γ ≡ γ .snd) → e ≡ idn x
    unit⁻-canonical x e abs = sym (rb e) ∙ abs (covar x)

    unit⁺-canonical : ∀ x (e : hom x x)
                    → (∀ t → act-π e t ≡ t .snd) → e ≡ idn x
    unit⁺-canonical x e abs = sym (rb e) ∙ abs (var x)
```

A candidate unit is an edge together with a proof that its action is
the identity action. It is an element of the fiber the unit tier
contracts. Such a candidate reaches `idn` two ways: through the
fiber's own projected unit, or straight through `rb`. Both routes
come from one function of the candidate, `route⁻` and `route⁺`
below.

The two routes agree naturally in a path between two candidates.
`route⁻-natural` and `route⁺-natural` prove this by induction on
that path. The detour through the projected unit then cancels
against the direct route. `unique-agrees⁻` and `unique-agrees⁺`
state that cancellation.

```agda
    route⁻ : ∀ x (c : fiber (coact-π {x} {x}) snd) → c .fst ≡ idn x
    route⁻ x c = sym (rb (c .fst)) ∙ (λ i → c .snd i (covar x))

    route⁺ : ∀ x (c : fiber (act-π {x} {x}) snd) → c .fst ≡ idn x
    route⁺ x c = sym (rb (c .fst)) ∙ (λ i → c .snd i (var x))

    route⁻-natural
      : ∀ x (c₀ c₁ : fiber (coact-π {x} {x}) snd) (γ : c₀ ≡ c₁)
      → route⁻ x c₀ ≡ ap fst γ ∙ route⁻ x c₁
    route⁻-natural x c₀ c₁ γ =
      J (λ c₁' γ' → route⁻ x c₀ ≡ ap fst γ' ∙ route⁻ x c₁')
        (sym (Path.unitl (route⁻ x c₀))) γ

    route⁺-natural
      : ∀ x (c₀ c₁ : fiber (act-π {x} {x}) snd) (γ : c₀ ≡ c₁)
      → route⁺ x c₀ ≡ ap fst γ ∙ route⁺ x c₁
    route⁺-natural x c₀ c₁ γ =
      J (λ c₁' γ' → route⁺ x c₀ ≡ ap fst γ' ∙ route⁺ x c₁')
        (sym (Path.unitl (route⁺ x c₀))) γ

    unique-agrees⁻
      : ∀ x (e : hom x x) (abs : ∀ γ → coact-π e γ ≡ γ .snd)
      → unit⁻-unique x e abs ∙ unit⁻-is-idn x ≡ unit⁻-canonical x e abs
    unique-agrees⁻ x e abs =
      ap (sym (ap fst γ) ∙_) (route⁻-natural x (unit-fiber⁻ x .center) c γ)
      ∙ Path.assoc (sym (ap fst γ)) (ap fst γ) (route⁻ x c)
      ∙ ap (_∙ route⁻ x c) (Path.invl (ap fst γ))
      ∙ Path.unitl (route⁻ x c)
      where
        c : fiber (coact-π {x} {x}) snd
        c = e , funext abs

        γ : unit-fiber⁻ x .center ≡ c
        γ = unit-fiber⁻ x .paths c

    unique-agrees⁺
      : ∀ x (e : hom x x) (abs : ∀ t → act-π e t ≡ t .snd)
      → unit⁺-unique x e abs ∙ unit⁺-is-idn x ≡ unit⁺-canonical x e abs
    unique-agrees⁺ x e abs =
      ap (sym (ap fst γ) ∙_) (route⁺-natural x (unit-fiber⁺ x .center) c γ)
      ∙ Path.assoc (sym (ap fst γ)) (ap fst γ) (route⁺ x c)
      ∙ ap (_∙ route⁺ x c) (Path.invl (ap fst γ))
      ∙ Path.unitl (route⁺ x c)
      where
        c : fiber (act-π {x} {x}) snd
        c = e , funext abs

        γ : unit-fiber⁺ x .center ≡ c
        γ = unit-fiber⁺ x .paths c
```

The coherence pins a readback family at the flanks. It reads the
family's value at each hand's projected unit. It transports that
value to `idn` through that hand's own absorption. It then asks the
family's own value at `idn` to agree with the transported value.

`flank⁻-of` and `flank⁺-of` compute the transported side.
`absorb-coh` states the agreement for both hands at once. The
stability tier wraps a readback family together with a witness of
this coherence inside contractibility. It does not assume that the
pair is a mere proposition on its own.

```agda
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

    absorb-coh : framing.readback-of G idn idn → Type (o ⊔ h)
    absorb-coh u =
      ∀ x → (u (idn x) ≡ flank⁻-of x (u (unit⁻ x)))
          × (u (idn x) ≡ flank⁺-of x (u (unit⁺ x)))

    is-stable : Type (o ⊔ h)
    is-stable = is-contr (Σ {A = framing.readback-of G idn idn} absorb-coh)

    is-stable-is-prop : is-prop is-stable
    is-stable-is-prop = is-contr-is-prop _
```

Wrapping the pair in contractibility matters, and is not decoration.
The coherence alone does not make the pair propositional as a
structural fact. Every value the coherence reads sits at an
endomorphism: `idn`, or one of the two projected units. A `half-twist` is
a self-path attached to every edge. Take a half-twist that vanishes at
every endomorphism, the hypothesis `coh-half-twist` calls `te`.

Composing it onto a readback family perturbs the family without
touching any value the coherence reads. The perturbed pair is
coherent again, by `coh-half-twist`. Suppose the pair type were a mere
proposition on its own. Then the perturbed pair and the original
pair would be equal. `half-adjoint-forces-truncation` reads that
equality apart.

It shows the half-twist is trivial everywhere, at every edge and not only
at the endomorphisms. Untruncated hom types can carry self-paths
that are not trivial. This route does not make the pair propositional
in general. This tier instead posits contractibility directly, as a
hypothesis about the graph. It does not derive contractibility from
the coherence.

```agda
    half-twist : Type (o ⊔ h)
    half-twist = ∀ {x y} (f : hom x y) → f ≡ f

    _∙ᵗ_ : framing.readback-of G idn idn → half-twist
         → framing.readback-of G idn idn
    (u ∙ᵗ t) f = u f ∙ t f

    half-adjoint : Type (o ⊔ h)
    half-adjoint = Σ {A = framing.readback-of G idn idn} absorb-coh

    module _ (t : half-twist) (te : ∀ x (e : hom x x) → t e ≡ refl) where

      agree : ∀ (u : framing.readback-of G idn idn) x (e : hom x x) → (u ∙ᵗ t) e ≡ u e
      agree u x e = ap (u e ∙_) (te x e) ∙ Path.unitr (u e)

      coh-half-twist : (u : framing.readback-of G idn idn)
                     → absorb-coh u → absorb-coh (u ∙ᵗ t)
      coh-half-twist u c x .fst =
        agree u x (idn x) ∙ c x .fst
        ∙ sym (ap (flank⁻-of x) (agree u x (unit⁻ x)))
      coh-half-twist u c x .snd =
        agree u x (idn x) ∙ c x .snd
        ∙ sym (ap (flank⁺-of x) (agree u x (unit⁺ x)))

    private
      cancel : ∀ {u} {A : Type u} {a b : A} (p : a ≡ b) (q : b ≡ b)
             → p ≡ p ∙ q → q ≡ refl
      cancel p q e =
        sym (Path.unitl q)
        ∙ ap (_∙ q) (sym (Path.invl p))
        ∙ sym (Path.assoc (sym p) p q)
        ∙ ap (sym p ∙_) (sym e)
        ∙ Path.invl p

    half-adjoint-forces-truncation
      : is-prop half-adjoint
      → (S : half-adjoint)
      → (t : half-twist) (te : ∀ x (e : hom x x) → t e ≡ refl)
      → ∀ {x y} (f : hom x y) → t f ≡ refl
    half-adjoint-forces-truncation P S t te {x} {y} f =
      cancel (S .fst f) (t f) (ap (λ w → w {x} {y} f) (ap fst step))
      where
        step : S ≡ (S .fst ∙ᵗ t , coh-half-twist t te (S .fst) (S .snd))
        step = P S _
```

## The dictionary's unital hands

Each hand's fibration wants a reflexive edge on its display, and the
chosen edge supplies one only where it absorbs. That absorption is the
hypothesis, and it is what makes the coslice and the slice displays
reflexive.

```agda
module hand⁻-unital {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x)
  (open chosen G idn) (open dict G idn)
  (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
          → is-contr (is-representable G (composite⁻ f g)))
  (open dict.hand⁻ G idn contr⁻)
  (absorb⁻ : ∀ {x y} (f : hom x y) → reflect f ≡ composite⁻ f (idn y))
  where

  coslice : ob → rx.disp graph h (o ⊔ h)
  coslice a .reflexive-graphᴰ.vtx z          = hom a z
  coslice a .reflexive-graphᴰ.edge y z p u w = reflect w ≡ composite⁻ u p
  coslice a .reflexive-graphᴰ.rx u           = absorb⁻ u

  coslice-fibration : ∀ a → rx.is-cov-fibration graph (coslice a)
  coslice-fibration _ _ _ p u = contr⁻ u p

  module F (a : ob) = rx.cov-fibration graph (coslice a) (coslice-fibration a)

  push-is-comp : ∀ a y z (p : hom y z) (u : hom a y) → F.push a y z p u ≡ u ⨾ p
  push-is-comp _ _ _ _ _ = refl

  lift-is-witness : ∀ a y z (p : hom y z) (u : hom a y)
                  → F.lift a y z p u ≡ reflect-⨾ u p
  lift-is-witness _ _ _ _ _ = refl
```

```agda
module hand⁺-unital {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x)
  (open chosen G idn) (open dict G idn)
  (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
          → is-contr (is-representable G (composite⁺ f g)))
  (open dict.hand⁺ G idn contr⁺)
  (absorb⁺ : ∀ {x y} (f : hom x y) → reflect f ≡ composite⁺ (idn x) f)
  where

  slice : ob → rx.disp graph h (o ⊔ h)
  slice c .reflexive-graphᴰ.vtx x          = hom x c
  slice c .reflexive-graphᴰ.edge x y p u w = reflect u ≡ composite⁺ p w
  slice c .reflexive-graphᴰ.rx u           = absorb⁺ u

  slice-fibration : ∀ c → rx.is-ctrv-fibration graph (slice c)
  slice-fibration _ _ _ p w = contr⁺ p w

  module F (c : ob) = rx.ctrv-fibration graph (slice c) (slice-fibration c)

  pull-is-comp : ∀ c x y (p : hom x y) (w : hom y c) → F.pull c x y p w ≡ p ⨾ w
  pull-is-comp _ _ _ _ _ = refl
```
