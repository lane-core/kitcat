The framed vocabulary over the carrier: two families of endo-edges
close the two ends of an argument, and every construction that reads
them takes them as explicit parameters. `framing⁻` holds what reads
`rx` alone, `framing⁺` what reads `corx` alone, and `framing`
their union together with the constructions that read both.

A `⁻`/`⁺` suffix is read in one of three registers, and they do not
agree with one another. `corx`, `rx` name the half-twist families:
`rx` fills `var`, `corx` fills `covar`. The framing register —
`cell` and `fiber` — is indexed by the argument side
the construction lives on: `⁻` is the coterm side, built through
`coact`, and `⁺` the term side, built through `act`. The composition
register — `composite`, `inj`, `is-composable` — is the polarity of
the hand, in the duploid sense. The last two registers are crossed:
the `⁺` hand is built from the coterm-side coaction and cuts through
`rx`, and the `⁻` hand cuts through `corx`. That crossing is
what the framing is, not an artefact of naming.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Framing where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; Π-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)
open import Core.Equiv.Base using (iso→equiv)
open import Core.Equiv.Properties using (is-contr-equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
```

## The negative family

`var` closes the term half. Holding it at its axiom leaves the
coterm-side action, so the coaction and the positive composite both
read `rx` and nothing else.

```agda
module framing⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x) where

  var : (x : ob) → term x
  var x = x , rx x

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (var x , γ)

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact f γ = γ .fst , coact-π f γ
```

A positive cut keeps its first factor reflected and absorbs the
second into the coterm, so it reads `rx` alone.

```agda
  inj⁺ : ∀ {x y z} → judgment x y → hom y z → judgment x z
  inj⁺ α p γ = α (γ .fst , coact p (γ .snd))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g = inj⁺ (reflect f) g

  is-composable⁺ : Type (o ⊔ h)
  is-composable⁺ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-representable G (composite⁺ f g)

  is-composable⁺-is-prop : reflect-is-embedding G → is-prop is-composable⁺
  is-composable⁺-is-prop S =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → S _
```

## The positive family

The mirror: `covar` closes the coterm half, and the term-side
action and the negative composite read `corx` alone.

```agda
module framing⁺ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (corx : (x : ob) → hom x x) where

  covar : (y : ob) → coterm y
  covar y = y , corx y

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (t , covar y)

  act : ∀ {x y} → hom x y → term x → term y
  act f t = t .fst , act-π f t

  inj⁻ : ∀ {x y z} → hom x y → judgment y z → judgment x z
  inj⁻ p β γ = β (act p (γ .fst) , γ .snd)

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g = inj⁻ f (reflect g)

  is-composable⁻ : Type (o ⊔ h)
  is-composable⁻ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → is-representable G (composite⁻ f g)

  is-composable⁻-is-prop : reflect-is-embedding G → is-prop is-composable⁻
  is-composable⁻-is-prop S =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → S _
```

## The full framing

```agda
module framing {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where

  open framing⁻ G rx public
  open framing⁺ G corx public

  axiom : (x : ob) → argument x x
  axiom x .fst = var x
  axiom x .snd = covar x

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)
```

Readback is the correctness equation of normalization by evaluation,
stated unit-free: `reflect` evaluates an edge into the judgment
domain, the axiom is the generic environment, and readback says
reification at the axiom retracts evaluation.

```agda
  readback-of : Type (o ⊔ h)
  readback-of = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f
```

Each side's cell carries one half-twist of each sign: the coterm-side
cell is the negative half-twist read through `act-π`, which holds the
positive one, and the term-side cell is the mirror. A pending read
meets a pending write, the cancellation performed and never named as
an edge of its own.

```agda
  cell⁻ : (x : ob) (γ : coterm x) → hom x (γ .fst)
  cell⁻ x γ = act-π (rx (γ .fst)) (x , γ .snd)

  cell⁺ : (x : ob) (t : term x) → hom (t .fst) x
  cell⁺ x t = coact-π (corx (t .fst)) (x , t .snd)
```

Where the edges form sets, the embedding condition reduces to
injectivity of transmission — evaluation of a reflection, the edge
surrounded by one half-twist of each sign.

```agda
  embedding-from-hom-sets
    : (∀ {x y} → is-set (hom x y))
    → (∀ {x y} {m n : hom x y} → eval (reflect m) ≡ eval (reflect n) → m ≡ n)
    → reflect-is-embedding G
  embedding-from-hom-sets hset inj =
    embedding-from-injective G hset (λ p → inj (ap eval p))
```

## Naturality of a half-twist

Each hand already carries one half-twist at its junction: the positive
composite reads its second factor at `var`, which holds `rx`, and the
negative composite reads its first factor at `covar`, which holds
`corx`. A half-twist may still flank either hand on either side, so six
pairings of a hand's two judgments are well typed. `own` gives each
half-twist the hand whose junction it does not fill. `alt` gives it the
hand whose junction already holds it, so that word carries the same
half-twist twice. `mixed` pairs a word of one hand with a word of the
other, which compares the two cuts rather than one half-twist.

```agda
  own⁻ own⁺ alt⁻ alt⁺ mixed⁻ mixed⁺ : ∀ {x y} → hom x y → Type (o ⊔ h)
  own⁻   {x} {y} m = centred G (composite⁻ (rx x) m) (composite⁻ m (rx y))
  own⁺   {x} {y} m = centred G (composite⁺ (corx x) m) (composite⁺ m (corx y))
  alt⁻   {x} {y} m = centred G (composite⁺ (rx x) m) (composite⁺ m (rx y))
  alt⁺   {x} {y} m = centred G (composite⁻ (corx x) m) (composite⁻ m (corx y))
  mixed⁻ {x} {y} m = centred G (composite⁻ (rx x) m) (composite⁺ m (corx y))
  mixed⁺ {x} {y} m = centred G (composite⁺ (corx x) m) (composite⁻ m (rx y))
```

The two tiers adopt the `own` reading, one per hand: every edge has a
contractible centred pair between the two flanks of its hand's half-twist.
Contractibility is a proposition, so each tier is one.

```agda
  is-natural⁻ : Type (o ⊔ h)
  is-natural⁻ = ∀ {x y} (m : hom x y) → is-contr (own⁻ m)

  is-natural⁺ : Type (o ⊔ h)
  is-natural⁺ = ∀ {x y} (m : hom x y) → is-contr (own⁺ m)

  is-natural⁻-is-prop : is-prop is-natural⁻
  is-natural⁻-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _

  is-natural⁺-is-prop : is-prop is-natural⁺
  is-natural⁺-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _
```

Read at the half-twist of its own hand, a tier's two judgments are one
term, so the pair is a diagonal and states no equation between
distinct composites. What the tier asks there is that the judgment's
own path space be contractible.

```agda
  diag⁻ : ∀ x → own⁻ (rx x)
              ≡ centred G (composite⁻ (rx x) (rx x))
                          (composite⁻ (rx x) (rx x))
  diag⁻ x = refl

  diag⁺ : ∀ x → own⁺ (corx x)
              ≡ centred G (composite⁺ (corx x) (corx x))
                          (composite⁺ (corx x) (corx x))
  diag⁺ x = refl

  diag-loop⁻ : is-natural⁻ → ∀ x
             → is-contr ( composite⁻ (rx x) (rx x)
                        ≡ composite⁻ (rx x) (rx x) )
  diag-loop⁻ N x = centred-loop G (N (rx x))

  diag-loop⁺ : is-natural⁺ → ∀ x
             → is-contr ( composite⁺ (corx x) (corx x)
                        ≡ composite⁺ (corx x) (corx x) )
  diag-loop⁺ N x = centred-loop G (N (corx x))
```

Dropping the contractible centre leaves the equation between the two
judgments. Stated that way, naturality is a family of paths in the
judgment type and asks no h-level.

```agda
  is-naturalᴶ⁻ : Type (o ⊔ h)
  is-naturalᴶ⁻ = ∀ {x y} (m : hom x y)
               → composite⁻ (rx x) m ≡ composite⁻ m (rx y)

  is-naturalᴶ⁺ : Type (o ⊔ h)
  is-naturalᴶ⁺ = ∀ {x y} (m : hom x y)
               → composite⁺ (corx x) m ≡ composite⁺ m (corx y)
```

## Duality

The opposite exchanges the argument halves, so a framing crosses it
with the two families swapped. The action maps exchange on the nose,
hence the absorption tiers do; evaluation at the axiom is
unmoved, so the readback predicate crosses unchanged; each cut
crosses to the other by exchanging the argument halves of a
representative.

```agda
module duality {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where

  op-eval : ∀ {x y} (f : hom y x)
          → framing.eval (opⱽ G) corx rx (virtual-graph.reflect (opⱽ G) f)
          ≡ framing.eval G rx corx (reflect f)
  op-eval f = refl

  op-readback : framing.readback-of G rx corx
              → framing.readback-of (opⱽ G) corx rx
  op-readback R f = R f

  op-readback⁻¹ : framing.readback-of (opⱽ G) corx rx
                → framing.readback-of G rx corx
  op-readback⁻¹ R f = R f

  op-composable⁺ : framing⁺.is-composable⁻ G corx
                 → framing⁻.is-composable⁺ (opⱽ G) corx
  op-composable⁺ C f g =
    C g f .fst , λ i γ → C g f .snd i (γ .snd , γ .fst)

  op-composable⁻ : framing⁻.is-composable⁺ G rx
                 → framing⁺.is-composable⁻ (opⱽ G) rx
  op-composable⁻ C f g =
    C g f .fst , λ i γ → C g f .snd i (γ .snd , γ .fst)
```

The contractible-cut forms cross the same way, through the same
argument-exchange equivalence on fibers.

```agda
  op-contr-cut⁺ : (∀ {x y z} (f : hom x y) (g : hom y z)
                   → is-contr (is-representable G (framing⁺.composite⁻ G corx f g)))
                → ∀ {x y z} (f : hom y x) (g : hom z y)
                → is-contr (is-representable (opⱽ G) (framing⁻.composite⁺ (opⱽ G) corx f g))
  op-contr-cut⁺ cc f g =
    is-contr-equiv
      (iso→equiv (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
                 (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
                 (λ _ → refl) (λ _ → refl))
      (cc g f)

  op-contr-cut⁻ : (∀ {x y z} (f : hom x y) (g : hom y z)
                   → is-contr (is-representable G (framing⁻.composite⁺ G rx f g)))
                → ∀ {x y z} (f : hom y x) (g : hom z y)
                → is-contr (is-representable (opⱽ G) (framing⁺.composite⁻ (opⱽ G) rx f g))
  op-contr-cut⁻ cc f g =
    is-contr-equiv
      (iso→equiv (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
                 (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
                 (λ _ → refl) (λ _ → refl))
      (cc g f)
```
