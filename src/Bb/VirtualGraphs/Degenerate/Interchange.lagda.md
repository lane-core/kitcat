Interchange and the frame. `framed-interchange` works over readback
and two contractible cuts: each hand gains one unit law, the two
cuts differ by the double half-twist, mixed associativity survives the
frame through readback, and no edge is a unit on both sides unless
the half-twists agree. `neutral-unit` takes the agreement of the two cut
judgments as a hypothesis over the tower and derives the four unit
laws, the identification of the half-twists, and a shared two-sided unit.
`tortile` transcribes the tortile half-twist laws per hand; each collapses
the framing to one edge.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Interchange where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Degenerate.Tower
```

## The interchange statement

Cutting through a pending read and cutting through a pending write
deliver the same judgment. Nothing below the hypothesis decides it:
the two composite judgments carry opposite windings at the junction,
and equating them is a coherence rather than a consequence.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x) where
  open framing G rx corx

  cuts-agree : Type (o ⊔ h)
  cuts-agree = ∀ {x y z} (f : hom x y) (g : hom y z)
                   → composite⁺ f g ≡ composite⁻ f g
```

## The framed carrier

Readback and two contractible cuts. Everything an h-category
derivation runs on transposes until its last step, which wants an
edge that is a unit on both sides; what stands in the way is the
double half-twist.

```agda
module framed-interchange {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (open framing G rx corx)
  (R : readback-of)
  (cc⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (composite⁺ f g)))
  (cc⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (composite⁻ f g)))
  where

  _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁺ g = cc⁺ f g .center .fst

  _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁻ g = cc⁻ f g .center .fst

  reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁺ g) ≡ composite⁺ f g
  reflect-⨾⁺ f g = cc⁺ f g .center .snd

  reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁻ g) ≡ composite⁻ f g
  reflect-⨾⁻ f g = cc⁻ f g .center .snd

  coact-covar : ∀ {x y} (f : hom x y) → coact f (covar y) ≡ (y , f)
  coact-covar {y = y} f = ap (y ,_) (R f)

  act-var : ∀ {x y} (f : hom x y) → act f (var x) ≡ (x , f)
  act-var {x} f = ap (x ,_) (R f)
```

A cut absorbs the half-twist filling its own slot, and only that one: the
positive cut closes its coterm at `corx` and so is right-unital
there, the negative one closes its term at `rx` and is
left-unital there.

```agda
  unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ corx y ≡ f
  unitr⁺ {x} {y} f =
    sym (R (f ⨾⁺ corx y))
    ∙ ap eval (reflect-⨾⁺ f (corx y))
    ∙ ap (λ c → reflect f (var x , c)) (coact-covar (corx y))
    ∙ R f

  unitl⁻ : ∀ {x y} (f : hom x y) → rx x ⨾⁻ f ≡ f
  unitl⁻ {x} {y} f =
    sym (R (rx x ⨾⁻ f))
    ∙ ap eval (reflect-⨾⁻ (rx x) f)
    ∙ ap (λ t → reflect f (t , covar y)) (act-var (rx x))
    ∙ R f
```

Cutting the inverse against the half-twist lands on whichever of the two
the hand absorbs, so the two answers are `rx` and `corx`.
Their gap is the double half-twist, and asking the cuts to agree is
asking for it to vanish.

```agda
  frame-⨾⁺ : (x : ob) → rx x ⨾⁺ corx x ≡ rx x
  frame-⨾⁺ x = unitr⁺ (rx x)

  frame-⨾⁻ : (x : ob) → rx x ⨾⁻ corx x ≡ corx x
  frame-⨾⁻ x = unitl⁻ (corx x)

  cuts-agree→involutive
    : (∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ⨾⁺ g)
    → (x : ob) → corx x ≡ rx x
  cuts-agree→involutive X x =
    sym (frame-⨾⁻ x) ∙ X (rx x) (corx x) ∙ frame-⨾⁺ x
```

Mixed associativity survives the frame: the two readings of one
reflection meet, through readback rather than the embedding condition.

```agda
  ⨾⁻-is-act : ∀ {w x y} (h : hom x y) (s : hom w x)
            → act-π h (w , s) ≡ s ⨾⁻ h
  ⨾⁻-is-act h s =
    (λ i → act-π h (act-var s (~ i)))
    ∙ sym (ap eval (reflect-⨾⁻ s h))
    ∙ R (s ⨾⁻ h)

  ⨾⁺-is-coact : ∀ {x y z} (f : hom x y) (k : hom y z)
              → coact-π f (z , k) ≡ f ⨾⁺ k
  ⨾⁺-is-coact f k =
    (λ i → coact-π f (coact-covar k (~ i)))
    ∙ sym (ap eval (reflect-⨾⁺ f k))
    ∙ R (f ⨾⁺ k)

  read⁺ : ∀ {u v w w'} (t : hom u v) (m : hom v w) (k : hom w w')
        → reflect m ((u , t) , (w' , k)) ≡ t ⨾⁻ (m ⨾⁺ k)
  read⁺ {u} {v} {w} {w'} t m k =
    (λ i → reflect m ((u , t) , coact-covar k (~ i)))
    ∙ (λ i → reflect-⨾⁺ m k (~ i) ((u , t) , covar w'))
    ∙ ⨾⁻-is-act (m ⨾⁺ k) t

  read⁻ : ∀ {u v w w'} (t : hom u v) (m : hom v w) (k : hom w w')
        → reflect m ((u , t) , (w' , k)) ≡ (t ⨾⁻ m) ⨾⁺ k
  read⁻ {u} {v} {w} {w'} t m k =
    (λ i → reflect m (act-var t (~ i) , (w' , k)))
    ∙ (λ i → reflect-⨾⁻ t m (~ i) (var u , (w' , k)))
    ∙ ⨾⁺-is-coact (t ⨾⁻ m) k

  mixed-assoc : ∀ {u v w w'} (t : hom u v) (m : hom v w) (k : hom w w')
              → t ⨾⁻ (m ⨾⁺ k) ≡ (t ⨾⁻ m) ⨾⁺ k
  mixed-assoc t m k = sym (read⁺ t m k) ∙ read⁻ t m k
```

A reflexivity edge serving both hands is available only where the
half-twist is an involution; otherwise the two missing laws are carried
by two edges.

```agda
  two-sided→involutive
    : (n : (x : ob) → hom x x)
    → (∀ {x z} (k : hom x z) → n x ⨾⁺ k ≡ k)
    → (∀ {w x} (t : hom w x) → t ⨾⁻ n x ≡ t)
    → (x : ob) → corx x ≡ rx x
  two-sided→involutive n l r = cuts-agree→involutive λ f g →
    sym (ap (f ⨾⁻_) (l g)) ∙ mixed-assoc f (n _) g ∙ ap (_⨾⁺ g) (r f)
```

Under the action identities the two cancellation axioms are the two
unit laws readback does not reach; the second cancellation reduces
exactly to right-cancellability of `_⨾⁻ corx`, and nothing in
readback or the cuts supplies that.

```agda
  act-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z) (t : term x)
         → act (f ⨾⁻ g) t ≡ act g (act f t)
  act-⨾⁻ f g t i = t .fst , reflect-⨾⁻ f g i (t , covar _)

  assoc⁻ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
         → f ⨾⁻ (g ⨾⁻ h) ≡ (f ⨾⁻ g) ⨾⁻ h
  assoc⁻ f g h =
    ap fst (is-contr→is-prop (cc⁻ (f ⨾⁻ g) h) a₁ (cc⁻ (f ⨾⁻ g) h .center))
    where
      a₁ : is-representable G (composite⁻ (f ⨾⁻ g) h)
      a₁ = f ⨾⁻ (g ⨾⁻ h)
         , reflect-⨾⁻ f (g ⨾⁻ h)
         ∙ (λ i γ → reflect-⨾⁻ g h i (act f (γ .fst) , γ .snd))
         ∙ (λ i γ → reflect h (act-⨾⁻ f g (γ .fst) (~ i) , γ .snd))

  module cancellation
    (cancel⁻ : ∀ {x z} (k : hom x z) → corx x ⨾⁺ k ≡ k)
    where

    factor : ∀ {w x z} (t : hom w x) (k : hom x z)
           → t ⨾⁻ k ≡ (t ⨾⁻ corx x) ⨾⁺ k
    factor {x = x} t k =
      sym (ap (t ⨾⁻_) (cancel⁻ k)) ∙ mixed-assoc t (corx x) k

    corx-absorbs : ∀ {w x} (t : hom w x)
                   → (t ⨾⁻ rx x) ⨾⁻ corx x ≡ t ⨾⁻ corx x
    corx-absorbs {x = x} t =
      sym (assoc⁻ t (rx x) (corx x))
      ∙ ap (t ⨾⁻_) (frame-⨾⁻ x)

    cancel⁺-from-cancellable
      : (∀ {w x} {a b : hom w x} → a ⨾⁻ corx x ≡ b ⨾⁻ corx x → a ≡ b)
      → ∀ {w x} (t : hom w x) → t ⨾⁻ rx x ≡ t
    cancel⁺-from-cancellable ι t = ι (corx-absorbs t)
```

With `corx` fixed, an edge satisfying readback against it is
exactly a left unit for the negative cut, and any right-cancellable
endomorphism makes such an edge unique: the negative half-twist is the
centre of a contractible fibre, with readback its defining property.

```agda
  readable : ∀ {x} → hom x x → Type (o ⊔ h)
  readable {x} r =
    ∀ {y} (f : hom x y) → reflect f ((x , r) , (y , corx y)) ≡ f

  readable→unitl⁻
    : ∀ {x} (r : hom x x) → readable r
    → ∀ {y} (f : hom x y) → r ⨾⁻ f ≡ f
  readable→unitl⁻ r P f = sym (⨾⁻-is-act f r) ∙ P f

  readable-unique
    : ∀ {x} (d : hom x x) → is-equiv (λ (g : hom x x) → g ⨾⁻ d)
    → (r r' : hom x x) → readable r → readable r' → r ≡ r'
  readable-unique d e r r' P P' = equiv→lc e
    (readable→unitl⁻ r P d ∙ sym (readable→unitl⁻ r' P' d))

  rx-readable : ∀ {x} → readable (rx x)
  rx-readable f = R f
```

## A neutral unit for both cuts

Under `cuts-agree`, over the tower with the four absorption
hypotheses: representation being unique, agreeing judgments have
equal representatives, so the two compositions are one; each hand's
own unit law transports to the other; the two half-twists are derived to
be equal; and their composite is a two-sided unit for both cuts.

```agda
module neutral-unit {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (open framing G rx corx)
  (pin⁻ : ∀ x → coact-π (corx x) ≡ cell⁻ x)
  (pin⁺ : ∀ x → act-π (rx x) ≡ cell⁺ x)
  (K⁻ : ∀ x → cell⁻ x ≡ snd) (K⁺ : ∀ x → cell⁺ x ≡ snd)
  (X : cuts-agree G rx corx)
  where

  open tower G rx corx S C⁺ C⁻
  open unital G rx corx S C⁺ C⁻ pin⁻ pin⁺ K⁻ K⁺

  ⨾-agree : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁺ g ≡ f ⨾⁻ g
  ⨾-agree f g = lc (reflect-⨾⁺ f g ∙ X f g ∙ sym (reflect-⨾⁻ f g))

  unitl⁺-rx : ∀ {x y} (g : hom x y) → rx x ⨾⁺ g ≡ g
  unitl⁺-rx g = ⨾-agree (rx _) g ∙ unitl⁻ g

  unitr⁻-corx : ∀ {x y} (f : hom x y) → f ⨾⁻ corx y ≡ f
  unitr⁻-corx f = sym (⨾-agree f (corx _)) ∙ unitr⁺ f

  half-twists-agree : ∀ x → rx x ≡ corx x
  half-twists-agree x = sym (unitr⁺ (rx x)) ∙ unitl⁺-rx (corx x)

  ι : (x : ob) → hom x x
  ι x = rx x ⨾⁺ corx x

  ι-rx : ∀ x → ι x ≡ rx x
  ι-rx = pair⁺

  ι-corx : ∀ x → ι x ≡ corx x
  ι-corx x = pair⁺ x ∙ half-twists-agree x

  ι-either : ∀ x → rx x ⨾⁻ corx x ≡ ι x
  ι-either x = sym (⨾-agree (rx x) (corx x))

  ι-unitl⁺ : ∀ {x y} (g : hom x y) → ι x ⨾⁺ g ≡ g
  ι-unitl⁺ {x} g = ap (_⨾⁺ g) (ι-rx x) ∙ unitl⁺-rx g

  ι-unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ ι y ≡ f
  ι-unitr⁺ {y = y} f = ap (f ⨾⁺_) (ι-corx y) ∙ unitr⁺ f

  ι-unitl⁻ : ∀ {x y} (g : hom x y) → ι x ⨾⁻ g ≡ g
  ι-unitl⁻ {x} g = sym (⨾-agree (ι x) g) ∙ ι-unitl⁺ g

  ι-unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ ι y ≡ f
  ι-unitr⁻ {y = y} f = sym (⨾-agree f (ι y)) ∙ ι-unitr⁺ f
```

So a framing with two genuinely distinct half-twists and a shared neutral
unit is not a shape that exists: either the half-twists differ and each
cut keeps its own one-sided unit, or they are identified and the two
cuts collapse to one with a two-sided unit.

## The tortile obligations

Each hand has a unit — the half-twist the other half carries — so the
tortile absorption demand is that the composite of the two half-twists
be that unit; read in either hand it forces the two half-twists to be one
edge. In the hand where a half-twist is the unit, the tortile naturality
law is two-sided unitality: the edge it speaks about occupies the
unit's place. Interchange asked at the half-twists alone is again their
identification, through the crossed pairings.

```agda
module tortile {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (open framing G rx corx)
  (pin⁻ : ∀ x → coact-π (corx x) ≡ cell⁻ x)
  (pin⁺ : ∀ x → act-π (rx x) ≡ cell⁺ x)
  (K⁻ : ∀ x → cell⁻ x ≡ snd) (K⁺ : ∀ x → cell⁺ x ≡ snd)
  where

  open tower G rx corx S C⁺ C⁻
  open unital G rx corx S C⁺ C⁻ pin⁻ pin⁺ K⁻ K⁺

  inverse⁻ : Type (o ⊔ h)
  inverse⁻ = ∀ x → rx x ⨾⁺ corx x ≡ corx x

  inverse⁺ : Type (o ⊔ h)
  inverse⁺ = ∀ x → rx x ⨾⁻ corx x ≡ rx x

  inverse⁻-collapses : inverse⁻ → ∀ x → rx x ≡ corx x
  inverse⁻-collapses H x = sym (pair⁺ x) ∙ H x

  inverse⁺-collapses : inverse⁺ → ∀ x → rx x ≡ corx x
  inverse⁺-collapses H x = sym (H x) ∙ pair⁻ x

  natural⁻ : Type (o ⊔ h)
  natural⁻ = ∀ {x y} (f : hom x y) → f ⨾⁺ corx y ≡ corx x ⨾⁺ f

  natural⁺ : Type (o ⊔ h)
  natural⁺ = ∀ {x y} (f : hom x y) → f ⨾⁻ rx y ≡ rx x ⨾⁻ f

  natural⁻-is-unitl : natural⁻ → ∀ {x y} (f : hom x y) → corx x ⨾⁺ f ≡ f
  natural⁻-is-unitl N f = sym (N f) ∙ unitr⁺ f

  natural⁺-is-unitr : natural⁺ → ∀ {x y} (f : hom x y) → f ⨾⁻ rx y ≡ f
  natural⁺-is-unitr N f = N f ∙ unitl⁻ f

  half-twist-interchange : Type (o ⊔ h)
  half-twist-interchange = ∀ x → rx x ⨾⁺ corx x ≡ rx x ⨾⁻ corx x

  half-twist-interchange-collapses : half-twist-interchange → ∀ x → rx x ≡ corx x
  half-twist-interchange-collapses H x = sym (pair⁺ x) ∙ H x ∙ pair⁻ x
```
