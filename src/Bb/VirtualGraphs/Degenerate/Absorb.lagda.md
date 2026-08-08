The absorption tier. Each action map closes one half of an argument
at a half-twist family; the tier asks the fiber of that map over the
second projection to be contractible, so the family has an edge acting
as the identity on its own half. A carrier meeting the tier supplies a
unit and its unit laws, which is what collapses the two-hand theory to
one composition, so the predicate lives here rather than beside the
framing vocabulary it is stated over.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Absorb where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.HLevel.Base using (Π-is-prop; is-prop-×)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Recognition
```

## The coterm-side tier

The fiber of the coterm-side action map over the second projection,
asked to be contractible. Its centre is the uniquely determined edge
acting as the identity on the coterm family — a right inverse of `rx`,
read through the argument.

```agda
module absorbing⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x) where

  open framing⁻ G rx

  is-absorbing⁻ : Type (o ⊔ h)
  is-absorbing⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) snd)

  is-absorbing⁻-is-prop : is-prop is-absorbing⁻
  is-absorbing⁻-is-prop = Π-is-prop λ _ → is-contr-is-prop _
```

## The term-side tier

The mirror, read through `act` and the positive family.

```agda
module absorbing⁺ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (corx : (x : ob) → hom x x) where

  open framing⁺ G corx

  is-absorbing⁺ : Type (o ⊔ h)
  is-absorbing⁺ = ∀ x → is-contr (fiber (act-π {x} {x}) snd)

  is-absorbing⁺-is-prop : is-prop is-absorbing⁺
  is-absorbing⁺-is-prop = Π-is-prop λ _ → is-contr-is-prop _
```

## Absorption from a cancellation

An action map that is the second projection at a family carries that
family's absorption on the whole argument half: the anonymous
endpoint never moves, so the path is the cancellation read at the
argument. The family is a parameter, since a tier's projected centre
absorbs the same way its half-twist does.

```agda
module from-cancel {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) (open framing G rx corx) where

  absorb⁻ : (e : (x : ob) → hom x x) → (∀ x → coact-π (e x) ≡ snd)
          → ∀ {y} (k : coterm y) → coact (e y) k ≡ k
  absorb⁻ e c {y} k i = k .fst , c y i k

  absorb⁺ : (e : (x : ob) → hom x x) → (∀ x → act-π (e x) ≡ snd)
          → ∀ {x} (t : term x) → act (e x) t ≡ t
  absorb⁺ e c {x} t i = t .fst , c x i t
```

## The opposite carrier

The opposite exchanges the two argument halves, so it exchanges the
two tiers on the nose.

```agda
module duality⁰ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where

  op-absorbing⁻ : absorbing⁻.is-absorbing⁻ (opⱽ G) corx
                ≡ absorbing⁺.is-absorbing⁺ G corx
  op-absorbing⁻ = refl

  op-absorbing⁺ : absorbing⁺.is-absorbing⁺ (opⱽ G) rx
                ≡ absorbing⁻.is-absorbing⁻ G rx
  op-absorbing⁺ = refl
```

## The tier at a candidate

The same fiber condition, anchored at a candidate framing instead of
the carrier's own. Read through the argument, the negative half asks
the first family for a unique right inverse and the positive half asks
the second family for a unique left one. Candidate readback then
forces each fiber point to the candidate's own component, and read at
the first family itself it is that family's own sandwich.

```agda
module candidate-absorbing {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open candidate G

  inv⁻ inv⁺ inv : frame → ob → Type (o ⊔ h)
  inv⁻ p x = is-contr (fiber (coact-π p {x} {x}) snd)
  inv⁺ p x = is-contr (fiber (act-π p {x} {x}) snd)
  inv p x = inv⁻ p x × inv⁺ p x

  inv⁻-is-prop : (p : frame) (x : ob) → is-prop (inv⁻ p x)
  inv⁻-is-prop p x = is-contr-is-prop _

  inv⁺-is-prop : (p : frame) (x : ob) → is-prop (inv⁺ p x)
  inv⁺-is-prop p x = is-contr-is-prop _

  inv-is-prop : (p : frame) (x : ob) → is-prop (inv p x)
  inv-is-prop p x = is-prop-× (inv⁻-is-prop p x) (inv⁺-is-prop p x)

  fiber⁻-point : (p : frame) → rb p → (x : ob)
               → (w : fiber (coact-π p {x} {x}) snd) → w .fst ≡ p .snd x
  fiber⁻-point p R x w = sym (R (w .fst)) ∙ happly (w .snd) (covar p x)

  fiber⁺-point : (p : frame) → rb p → (x : ob)
               → (w : fiber (act-π p {x} {x}) snd) → w .fst ≡ p .fst x
  fiber⁺-point p R x w = sym (R (w .fst)) ∙ happly (w .snd) (var p x)

  self-read : (p : frame) → rb p → (x : ob)
            → reflect (p .fst x) (var p x , covar p x) ≡ p .fst x
  self-read p R x = R (p .fst x)
```

## Absorption pins the chosen family

The held slot takes both its arguments from one family of
endo-edges. Absorption is the claim that two elements of the
resulting function type agree. One reads the family back through the
held slot. The other reads the coterm's own edge out directly.

```agda
module absorb {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  flank : Type (o ⊔ h)
  flank = (x : ob) (γ : coterm x) → hom x (γ .fst)

  held : ((x : ob) → hom x x) → flank
  held i x γ = reflect (i x) ((x , i x) , γ)

  cut : flank
  cut x γ = γ .snd

  absorbs : Type (o ⊔ h)
  absorbs = held idn ≡ cut
```

`held` reads the family back at every point. `cut` never mentions the
family. A self-path of the family already traces a loop of `held`
against a fixed target.

A propositional predicate that delivers absorption cannot distinguish
the family from any point on that loop. A witness at one endpoint
then slides along the loop to a witness at every other point. The
resulting square pins the loop to the constant path. This holds for
any packaging of the predicate, with no further hypothesis on the
carrier.

```agda
module obstruction {o h ℓ} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) (open absorb G idn)
  (P : ((x : ob) → hom x x) → Type ℓ)
  (P-prop : (i : (x : ob) → hom x x) → is-prop (P i))
  (pin : (i : (x : ob) → hom x x) → P i → held i ≡ cut)
  where

  drift : (p : P idn) (q : idn ≡ idn)
        → PathP (λ i → held (q i) ≡ cut) (pin idn p) (pin idn p)
  drift p q i = pin (q i) (is-prop→PathP (λ j → P-prop (q j)) p p i)

  rigid : (p : P idn) (q : idn ≡ idn) → ap held q ≡ refl
  rigid p q =
    Path.loop-refl (sym (pin idn p)) (ap held q) (λ i j → drift p q i (~ j))
```
