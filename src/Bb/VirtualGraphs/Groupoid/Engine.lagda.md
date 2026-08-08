The path-groupoid witness for each of the five chosen-edge theory
modules that carries one. At the discrete path groupoid on an
arbitrary type, representability is total, so every hypothesis
telescope those modules state is inhabited untruncated — no h-level
condition on the carrier and no truncation of any tier. The five
witnesses are independent constructions, each opening its own
reflexive carrier.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Groupoid.Engine where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat.Type using (Z)
open import Core.Kan using (_∙_; module Path; module pcom; module cat)
open import Core.Transport.Base using (transport; transport⁻)
open import Core.Transport.J using (subst; J; J-refl)
open import Core.Transport.Properties using (transport-transport⁻)
open import Core.Retract using (_◁_; section; retraction; is-retract; Σ-◁; ◁→is-hlevel)
open import Core.Equiv.Base
  using (_≃_; is-equiv; eqv-fibers; iso→equiv; is-contr-equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)

open import Bb.VirtualGraphs.Framing using (module framing)
open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Degenerate.Chosen
open import Bb.VirtualGraphs.Embedding using (is-representable)

import Bb.VirtualGraphs.Degenerate.Absorb as Absorb
import Bb.VirtualGraphs.Degenerate.UnitShape as UnitShape
import Bb.VirtualGraphs.Degenerate.CrossedUnit as CrossedUnit
import Bb.VirtualGraphs.Degenerate.Reflexive as Reflexive
import Bb.VirtualGraphs.Degenerate.Stable as Stable
import Bb.VirtualGraphs.Degenerate.Curried as Curried
```

## Shared path algebra

A family of self-maps on paths is determined by its value at
reflexivity — singleton contraction along the identity type. Fixing
a value there (`t₀`) makes the package of a family together with an
agreement of its own reflexivity-value against `t₀` a retract of a
contractible anchor, so the package is contractible and restriction
to the diagonal is an equivalence.

```agda
private
  path-◁ : ∀ {u} {X Y : Type u} → X ≡ Y → X ◁ Y
  path-◁ P .section    = transport P
  path-◁ P .retraction = transport⁻ P
  path-◁ P .is-retract = transport-transport⁻ P

  module pin {u} {A : Type u}
    (T : ∀ {x y : A} → x ≡ y → x ≡ y)
    (t₀ : ∀ x → T (refl {x = x}) ≡ refl)
    where

    refl-values : Type u
    refl-values = ∀ x → T (refl {x = x}) ≡ refl

    readback : Type u
    readback = ∀ x y (p : x ≡ y) → T p ≡ p

    pinned : readback → Type u
    pinned rd = ∀ x → rd x x refl ≡ t₀ x

    package : Type u
    package = Σ rd ∶ readback , pinned rd

    anchor : Type u
    anchor = Σ v ∶ refl-values , (∀ x → v x ≡ t₀ x)

    at-refl : readback → refl-values
    at-refl rd x = rd x x refl

    extend : refl-values → readback
    extend v x y p = J (λ _ q → T q ≡ q) (v x) p

    extend-refl : ∀ v x → extend v x x refl ≡ v x
    extend-refl v x = J-refl (λ _ q → T q ≡ q) (v x)

    extend-glue
      : ∀ rd x y (p : x ≡ y)
      → extend (at-refl rd) x y p ≡ rd x y p
    extend-glue rd x y p =
      J (λ y' q → extend (at-refl rd) x y' q ≡ rd x y' q)
        (extend-refl (at-refl rd) x) p

    extend-retract : ∀ rd → extend (at-refl rd) ≡ rd
    extend-retract rd i x y p = extend-glue rd x y p i

    readback-◁ : readback ◁ refl-values
    readback-◁ .section    = at-refl
    readback-◁ .retraction = extend
    readback-◁ .is-retract = extend-retract

    pinned-line : ∀ v → pinned (extend v) ≡ (∀ x → v x ≡ t₀ x)
    pinned-line v i = ∀ x → extend-refl v x i ≡ t₀ x

    package-◁ : package ◁ anchor
    package-◁ = Σ-◁ readback-◁ λ v → path-◁ (pinned-line v)

    anchor-contr : is-contr anchor
    anchor-contr .center = t₀ , λ _ → refl
    anchor-contr .paths (v , k) i =
      (λ x → k x (~ i)) , λ x j → k x (~ i ∨ j)

    pin-contr : is-contr package
    pin-contr = ◁→is-hlevel Z package-◁ anchor-contr
```

## Doubling: absorption forces the loop trivial

At the discrete path groupoid, reflexivity absorbs outright: holding
it in both slots of the ternary composite leaves the composite
standing on its third argument, with no truncation hypothesis on the
carrier. Reading the resulting family back at the axiom half of each
coterm restricts it to pointwise squaring, so `UnitShape`'s rigidity
theorem, instantiated here, forces every self-path of the
reflexivity family to be annihilated by doubling.

```agda
module doubling {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob          = A
  PG .virtual-graph.hom x y     = x ≡ y
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  rx : (x : A) → x ≡ x
  rx x = refl

  pg-absorbs : Absorb.absorb.absorbs PG rx
  pg-absorbs = funext λ x → funext λ γ → pcom.ideml (γ .snd)

  restrict : Absorb.absorb.flank PG rx → (x : A) → x ≡ x
  restrict f x = f x (x , refl)

  dbl : ((x : A) → x ≡ x) → (x : A) → x ≡ x
  dbl i = restrict (Absorb.absorb.held PG rx i)

  double : (i : (x : A) → x ≡ x) (x : A) → dbl i x ≡ i x ∙ i x
  double i x =
    pcom.unique (sym (i x)) (i x) refl
      (i x ∙ i x ∙ refl , cat.lcoh (i x) (i x) refl)
    ∙ Path.lwhisker (i x) (Path.unitr (i x))

  module rigidity {ℓ} (P : ((x : A) → x ≡ x) → Type ℓ)
    (P-prop : (i : (x : A) → x ≡ x) → is-prop (P i))
    (discharge : (i : (x : A) → x ≡ x)
               → P i → Absorb.absorb.held PG rx i ≡ Absorb.absorb.cut PG rx)
    where

    doubling-rigid : (p : P rx) (q : rx ≡ rx) → ap dbl q ≡ refl
    doubling-rigid p q i j =
      restrict (Absorb.obstruction.rigid PG rx P P-prop discharge p q i j)
```

## Crossed: the term hand's fiber, at an arbitrary chosen family

Nothing distinguishes reflexivity here: `a` is any family of
endo-edges. The coterm hand's own unit fiber produces a filler edge,
and the term hand's tier — stated by `CrossedUnit` over that filler,
not over the chosen family a second time — has the chosen family
itself as its unique inhabitant. The two flank arrangements one
ternary composite admits, related by `pcom.lr`, carry the coterm
hand's centre straight into the term hand's fiber.

```agda
module crossed-groupoid {u} {A : Type u} (a : (x : A) → x ≡ x) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob          = A
  PG .virtual-graph.hom x y     = x ≡ y
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  open virtual-graph PG using (term; coterm; judgment; reflect)
  open chosen PG a using (var; covar; coact-π)

  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = x , refl
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = y , refl
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  recentre : ∀ {ℓ} {T : Type ℓ} → is-contr T → T → is-contr T
  recentre c t .center = t
  recentre c t .paths s = sym (c .paths t) ∙ c .paths s

  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  slot≃ : ∀ {x y}
        → judgment x y ≃ ((t : term x) (γ : coterm y) → t .fst ≡ γ .fst)
  slot≃ = iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                    (λ _ → refl) (λ _ → refl)

  slot-swap≃ : ∀ {x y}
             → judgment x y ≃ ((γ : coterm y) (t : term x) → t .fst ≡ γ .fst)
  slot-swap≃ = iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                         (λ _ → refl) (λ _ → refl)

  coact-π-equiv : ∀ x → is-equiv (coact-π {x} {x})
  coact-π-equiv x =
    ( (reflect , reflect-equiv)
    ∙e slot≃
    ∙e Π-contr-dom (recentre (term-contr x) (var x)) ) .snd

  PG-unital⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
  PG-unital⁻ x = eqv-fibers (coact-π-equiv x) snd

  module F = CrossedUnit.crossed.filler PG a PG-unital⁻
  open F using (unit⁻; covar⁻; act-π⁻; is-unital⁺; unit⁺; unit⁺-unique)

  act-π⁻-equiv : ∀ x → is-equiv (act-π⁻ {x} {x})
  act-π⁻-equiv x =
    ( (reflect , reflect-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (covar⁻ x)) ) .snd

  PG-unital⁺ : is-unital⁺
  PG-unital⁺ x = eqv-fibers (act-π⁻-equiv x) snd

  centre⁻ : ∀ x → coact-π (unit⁻ x) ≡ snd
  centre⁻ x = PG-unital⁻ x .center .snd

  centre⁻-pt : ∀ x → pcom.composite (sym (a x)) (unit⁻ x) refl ≡ refl
  centre⁻-pt x i = centre⁻ x i (x , refl)

  at-axiom : ∀ x → act-π⁻ (a x) (x , refl) ≡ refl
  at-axiom x = pcom.lr (a x) (unit⁻ x) ∙ centre⁻-pt x

  chosen-absorbs⁺ : ∀ x → act-π⁻ (a x) ≡ snd
  chosen-absorbs⁺ x = funext λ t →
    subst (λ s → act-π⁻ (a x) s ≡ s .snd)
          (term-contr x .paths t) (at-axiom x)

  crossed : ∀ x → a x ≡ unit⁺ PG-unital⁺ x
  crossed x = unit⁺-unique PG-unital⁺ x (a x) (chosen-absorbs⁺ x)
```

## Reflexive: the chosen edge absorbing outright

At the discrete path groupoid, reflexivity's own action is already
the identity action on each hand — `pcom`'s two idempotence laws —
so `Reflexive`'s hypotheses hold with the chosen edge as the witness
directly, no unit-fiber detour needed to state them. Restriction of
readback to the identities is separately an equivalence: a family of
self-maps on paths is determined by its value at reflexivity, so
every edge absorbing on either hand equals the chosen one by that
readback alone.

```agda
module reflexive-groupoid {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob          = A
  PG .virtual-graph.hom x y     = x ≡ y
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  rx : (x : A) → x ≡ x
  rx x = refl

  open virtual-graph PG using (term; coterm; judgment; reflect)
  open chosen PG rx using (var; covar; coact-π; act-π; eval)

  absorb⁻ : ∀ x (γ : coterm x) → coact-π (rx x) γ ≡ γ .snd
  absorb⁻ x γ = pcom.ideml (γ .snd)

  absorb⁺ : ∀ x (t : term x) → act-π (rx x) t ≡ t .snd
  absorb⁺ x t = pcom.idemr (t .snd)

  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = x , refl
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = y , refl
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  coact-π-equiv : ∀ x → is-equiv (coact-π {x} {x})
  coact-π-equiv x =
    ( (reflect , reflect-equiv)
    ∙e iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                 (λ _ → refl) (λ _ → refl)
    ∙e Π-contr-dom {B = λ t → (γ : coterm x) → t .fst ≡ γ .fst} (term-contr x) ) .snd

  act-π-equiv : ∀ x → is-equiv (act-π {x} {x})
  act-π-equiv x =
    ( (reflect , reflect-equiv)
    ∙e iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                 (λ _ → refl) (λ _ → refl)
    ∙e Π-contr-dom {B = λ γ → (t : term x) → t .fst ≡ γ .fst} (coterm-contr x) ) .snd

  PG-unital⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)
  PG-unital⁻ x = eqv-fibers (coact-π-equiv x) snd

  PG-unital⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) snd)
  PG-unital⁺ x = eqv-fibers (act-π-equiv x) snd

  T : ∀ {x y : A} → x ≡ y → x ≡ y
  T {x} {y} p = emb p x refl y refl

  t₀ : ∀ (x : A) → T (refl {x = x}) ≡ refl
  t₀ x = pcom.unit refl

  rb≃ : framing.readback-of PG rx rx ≃ (∀ (x y : A) (p : x ≡ y) → T p ≡ p)
  rb≃ = iso→equiv (λ u _ _ p → u p) (λ rd p → rd _ _ p) (λ _ → refl) (λ _ → refl)

  at-refl-equiv : is-equiv (pin.at-refl T t₀)
  at-refl-equiv =
    iso→equiv (pin.at-refl T t₀) (pin.extend T t₀)
              (pin.extend-retract T t₀)
              (λ v → funext (pin.extend-refl T t₀ v)) .snd

  restrict-equiv : is-equiv (Reflexive.restrict PG rx absorb⁻ absorb⁺)
  restrict-equiv = (rb≃ ∙e (pin.at-refl T t₀ , at-refl-equiv)) .snd

  module R = Reflexive.redundancy PG rx absorb⁻ absorb⁺ restrict-equiv
```

## Emb-action stability, every packaging at once

The same carrier inhabits `Stable`'s three formulations of the unit
tier side by side. Each hand's action at reflexivity is already an
equivalence — the same two idempotence laws as above — and the
composite of reflexivity with itself already represents its own
reflection, so the emb-action package holds with no readback
consulted. Restriction of readback to the identities is separately
an equivalence, by the same singleton-contraction argument as the
previous section, so all three tiers are inhabited untruncated,
independently of each other, exactly as the theory module keeps
them.

```agda
module stable-groupoid {u} (A : Type u) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob          = A
  PG .virtual-graph.hom x y     = x ≡ y
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  rx : (x : A) → x ≡ x
  rx x = refl

  open virtual-graph PG using (hom; term; coterm; judgment; reflect)
  open chosen PG rx
    using (var; covar; argue; coact-π; act-π; coact; act; composite⁻; composite⁺; eval)

  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (reflect {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  eqv⁻ : ∀ {x v : A} → is-equiv (λ (b : hom x v) → coact-π (rx x) (v , b))
  eqv⁻ = iso→equiv _ (λ b → b) (λ b → pcom.ideml b) (λ b → pcom.ideml b) .snd

  eqv⁺ : ∀ {w x : A} → is-equiv (λ (a : hom w x) → act-π (rx x) (w , a))
  eqv⁺ = iso→equiv _ (λ a → a) (λ a → pcom.idemr a) (λ a → pcom.idemr a) .snd

  contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable PG (composite⁻ f g))
  contr⁻ f g = eqv-fibers reflect-equiv (composite⁻ f g)

  contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
         → is-contr (is-representable PG (composite⁺ f g))
  contr⁺ f g = eqv-fibers reflect-equiv (composite⁺ f g)

  coact-idn : ∀ {y : A} (e : coterm y) → coact (rx y) e ≡ e
  coact-idn e i = e .fst , pcom.ideml (e .snd) i

  act-idn : ∀ {x : A} (t : term x) → act (rx x) t ≡ t
  act-idn t i = t .fst , pcom.idemr (t .snd) i

  rep-idem⁻ : ∀ x → reflect (rx x) ≡ composite⁻ (rx x) (rx x)
  rep-idem⁻ x i γ = reflect (rx x) (argue (γ .fst) (coact-idn (γ .snd) (~ i)))

  rep-idem⁺ : ∀ x → reflect (rx x) ≡ composite⁺ (rx x) (rx x)
  rep-idem⁺ x i γ = reflect (rx x) (argue (act-idn (γ .fst) (~ i)) (γ .snd))

  module Unt = Stable.unital PG rx contr⁻ contr⁺ eqv⁻ eqv⁺ rep-idem⁻ rep-idem⁺

  T : ∀ {x y : A} → x ≡ y → x ≡ y
  T {x} {y} p = emb p x refl y refl

  t₀ : ∀ (x : A) → T (refl {x = x}) ≡ refl
  t₀ x = pcom.unit refl

  stable-package
    : (τ₀ : ∀ (x : A) → T (refl {x = x}) ≡ refl)
    → is-contr (Σ rd ∶ (∀ (x y : A) (p : x ≡ y) → T p ≡ p) , (∀ x → rd x x refl ≡ τ₀ x))
  stable-package τ₀ = pin.pin-contr T τ₀

  bridge
    : (τ₀ : ∀ x → eval (reflect (rx x)) ≡ rx x)
    → (Σ v ∶ framing.readback-of PG rx rx , (∀ x → v (rx x) ≡ τ₀ x))
    ≃ (Σ rd ∶ (∀ (x y : A) (p : x ≡ y) → T p ≡ p) , (∀ x → rd x x refl ≡ τ₀ x))
  bridge τ₀ = iso→equiv (λ (v , k) → (λ _ _ p → v p) , k)
                        (λ (rd , k) → (λ {x} {y} p → rd x y p) , k)
                        (λ _ → refl) (λ _ → refl)

  PG-stable : Unt.is-stable
  PG-stable = is-contr-equiv (bridge Unt.canonical-flank⁻) (stable-package Unt.canonical-flank⁻)

  PG-stable⁺ : Unt.is-stable⁺
  PG-stable⁺ = is-contr-equiv (bridge Unt.canonical-flank⁺) (stable-package Unt.canonical-flank⁺)

  PG-stable-pair : Unt.is-stable-pair
  PG-stable-pair = PG-stable , PG-stable⁺

  rb≃ : framing.readback-of PG rx rx ≃ (∀ (x y : A) (p : x ≡ y) → T p ≡ p)
  rb≃ = iso→equiv (λ v _ _ p → v p) (λ rd p → rd _ _ p) (λ _ → refl) (λ _ → refl)

  at-refl-equiv : is-equiv (pin.at-refl T t₀)
  at-refl-equiv =
    iso→equiv (pin.at-refl T t₀) (pin.extend T t₀)
              (pin.extend-retract T t₀)
              (λ v → funext (pin.extend-refl T t₀ v)) .snd

  PG-is-stable : Stable.stable.is-stable PG rx
  PG-is-stable = (rb≃ ∙e (pin.at-refl T t₀ , at-refl-equiv)) .snd

  PG-composable : Stable.is-composable PG rx
  PG-composable = contr⁻ , contr⁺

  PG-unital : Stable.is-unital PG rx
  PG-unital = eqv⁻ , eqv⁺ , rep-idem⁻ , rep-idem⁺
```

## Curried: the two-string presentation at the discrete groupoid

The curried presentation reduces, at the path groupoid, to the same
representability: `yon-unbiased.emb` is total, so both composability
conditions hold at every string, not only at the ones a composable
pair spans. Both absorptions are `pcom`'s idempotence laws again, one
per slot, and readback is `pcom.unit` — the ternary composite with
both flanks reflexive.

```agda
module curried-groupoid {u} (A : Type u) where

  E : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  E = yon-unbiased.emb {A = λ _ → A}

  E-equiv : {x y : A} → is-equiv (E {x} {y})
  E-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  rx : (x : A) → x ≡ x
  rx x = refl

  module V = Curried.vgraph A (λ x y → x ≡ y) rx E
  open V using (yon; noy; ev; E▿; E▵)

  pull-contr : ∀ {x y z : A} (f : x ≡ y) (g : y ≡ z)
             → is-contr (fiber (E {x} {z}) (E▿ f g))
  pull-contr f g = eqv-fibers E-equiv (E▿ f g)

  push-contr : ∀ {x y z : A} (f : x ≡ y) (g : y ≡ z)
             → is-contr (fiber (E {x} {z}) (E▵ f g))
  push-contr f g = eqv-fibers E-equiv (E▵ f g)

  module H = V.hands pull-contr push-contr
  open H using (_⨾▿_; _⨾▵_; noy-composite; yon-composite)

  noy-refl : ∀ {x t : A} (b : x ≡ t) → noy (rx x) t b ≡ b
  noy-refl b = pcom.ideml b

  yon-refl : ∀ {x w : A} (a : w ≡ x) → yon (rx x) w a ≡ a
  yon-refl a = pcom.idemr a

  pull-eqv : ∀ {x t : A} → is-equiv (noy (rx x) t)
  pull-eqv = iso→equiv _ (λ b → b) noy-refl noy-refl .snd

  push-eqv : ∀ {x w : A} → is-equiv (yon (rx x) w)
  push-eqv = iso→equiv _ (λ a → a) yon-refl yon-refl .snd

  collapse▿ : ∀ {x : A} → E▿ (rx x) (rx x) ≡ E (rx x)
  collapse▿ i w a t b = E refl w a t (noy-refl b i)

  collapse▵ : ∀ {x : A} → E▵ (rx x) (rx x) ≡ E (rx x)
  collapse▵ i w a t b = E refl w (yon-refl a i) t b

  idem▿ : ∀ {x : A} → rx x ⨾▿ rx x ≡ rx x
  idem▿ {x} = ap fst (pull-contr (rx x) (rx x) .paths (rx x , sym collapse▿))

  idem▵ : ∀ {x : A} → rx x ⨾▵ rx x ≡ rx x
  idem▵ {x} = ap fst (push-contr (rx x) (rx x) .paths (rx x , sym collapse▵))

  module U = H.unital pull-eqv push-eqv idem▿ idem▵
  open U using
    (coincide; absorb▿; absorb▵; shrink▿; emb-image-contr▿; shrink▵;
     emb-image-contr▵; flank▿; flank▵; flank-pin)

  readback : ∀ {x y : A} (f : x ≡ y) → ev f ≡ f
  readback f = pcom.unit f

  module S = H.stable readback
  open S using (comp-eq▿; comp-eq▵; unitr▿; unitl▵)
```
