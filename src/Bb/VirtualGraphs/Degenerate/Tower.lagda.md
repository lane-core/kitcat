The absorption layer over the tower. Both modules take the collapse
as a hypothesis: `K⁻` and `K⁺` say each twist cell is the second
projection, which is the twist acting as the identity. From that the
two absorptions follow, and from the absorptions each hand gains its
near unit law.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Tower where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.HLevel.Base using (loops→is-set)
open import Core.Transport.J using (subst)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Naturality
```

## Absorption from the pin and K hypotheses

Pinning each half-twist to its side's cell and trivialising that cell is
two hypotheses per side, and together they say each centre is the
half-twist filling the other slot — the half-twists mutually inverse. The
absorptions consume no tier.

```agda
module absorption {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (open framing G rx corx)
  (pin⁻ : ∀ x → coact-π (corx x) ≡ cell⁻ x)
  (pin⁺ : ∀ x → act-π (rx x) ≡ cell⁺ x)
  (K⁻ : ∀ x → cell⁻ x ≡ snd) (K⁺ : ∀ x → cell⁺ x ≡ snd) where

  open from-cancel G rx corx using () renaming (absorb⁻ to abs⁻; absorb⁺ to abs⁺)

  absorb⁻ : ∀ {y} (k : coterm y) → coact (corx y) k ≡ k
  absorb⁻ = abs⁻ corx (λ y → pin⁻ y ∙ K⁻ y)

  absorb⁺ : ∀ {x} (t : term x) → act (rx x) t ≡ t
  absorb⁺ = abs⁺ rx (λ x → pin⁺ x ∙ K⁺ x)
```

## Near unit laws from the absorptions

Where the cancellation is the identity — the half-twists mutually
inverse, with no readback in sight — each hand gains exactly one
unit law: the positive a right unit at `corx`, the negative a left
unit at `rx`. The edge each gains is the other hand's composite
of the pair, and the crossed pairings feed `collapse⁺/⁻` above.

```agda
module unital {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (open framing G rx corx)
  (pin⁻ : ∀ x → coact-π (corx x) ≡ cell⁻ x)
  (pin⁺ : ∀ x → act-π (rx x) ≡ cell⁺ x)
  (K⁻ : ∀ x → cell⁻ x ≡ snd) (K⁺ : ∀ x → cell⁺ x ≡ snd) where

  open transfer G rx corx S C⁺ C⁻
    using (_⨾⁺_; _⨾⁻_; lc; reflect-⨾⁺; reflect-⨾⁻; loop⁻; loop⁺;
           unitr⁻-law; unitl⁺-law)
  open absorption G rx corx pin⁻ pin⁺ K⁻ K⁺ public

  unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ corx y ≡ f
  unitr⁺ f = lc
    ( reflect-⨾⁺ f (corx _)
    ∙ (λ i γ → reflect f (γ .fst , absorb⁻ (γ .snd) i)) )

  unitl⁻ : ∀ {x y} (g : hom x y) → rx x ⨾⁻ g ≡ g
  unitl⁻ g = lc
    ( reflect-⨾⁻ (rx _) g
    ∙ (λ i γ → reflect g (absorb⁺ (γ .fst) i , γ .snd)) )

  pair⁻ : ∀ x → rx x ⨾⁻ corx x ≡ corx x
  pair⁻ x = unitl⁻ (corx x)

  pair⁺ : ∀ x → rx x ⨾⁺ corx x ≡ rx x
  pair⁺ x = unitr⁺ (rx x)
```

Absorption trivializes one flank of each hand at the judgment level:
the negative hand's leading half-twist drops out of the composite, and the
positive hand's trailing one does the same.

```agda
  unitlᴶ⁻ : ∀ {x y} (m : hom x y) → composite⁻ (rx x) m ≡ reflect m
  unitlᴶ⁻ m i γ = reflect m (absorb⁺ (γ .fst) i , γ .snd)

  unitrᴶ⁺ : ∀ {x y} (m : hom x y) → composite⁺ m (corx y) ≡ reflect m
  unitrᴶ⁺ m i γ = reflect m (γ .fst , absorb⁻ (γ .snd) i)
```

Each hand's remaining flank is then the unit law the framing
withholds, so the naturality equation is exactly that law. The near
unit law also carries a tier's loop space onto the loop space at an
arbitrary edge, so each tier makes the hom types sets.

```agda
  module natural where

    hom-set⁻ : is-natural⁻ → ∀ {x y} → is-set (hom x y)
    hom-set⁻ N = loops→is-set λ m →
      subst (λ z → is-prop (z ≡ z)) (unitl⁻ m) (is-contr→is-prop (loop⁻ N m))

    hom-set⁺ : is-natural⁺ → ∀ {x y} → is-set (hom x y)
    hom-set⁺ N = loops→is-set λ m →
      subst (λ z → is-prop (z ≡ z)) (unitr⁺ m) (is-contr→is-prop (loop⁺ N m))

    farᴶ⁻ : is-naturalᴶ⁻ → ∀ {x y} (m : hom x y)
          → composite⁻ m (rx y) ≡ reflect m
    farᴶ⁻ q m = sym (q m) ∙ unitlᴶ⁻ m

    farᴶ⁺ : is-naturalᴶ⁺ → ∀ {x y} (m : hom x y)
          → composite⁺ (corx x) m ≡ reflect m
    farᴶ⁺ q m = q m ∙ unitrᴶ⁺ m

    unitr⁻ : is-naturalᴶ⁻ → unitr⁻-law
    unitr⁻ q {y = y} m = lc (reflect-⨾⁻ m (rx y) ∙ farᴶ⁻ q m)

    unitl⁺ : is-naturalᴶ⁺ → unitl⁺-law
    unitl⁺ q {x} m = lc (reflect-⨾⁺ (corx x) m ∙ farᴶ⁺ q m)
```
