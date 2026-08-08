The readback-free tower: each hand's composition is the
representative of its own cut, the embedding condition makes it
well defined, and associativity follows from a fiber path. Each
hand consumes only the half-twist its cut reads — `tower⁺` takes `rx`
alone and `tower⁻` takes `corx` alone — and `tower` joins them
with the mixed word, the withheld word `associates` and its
closures, and the coherence square of a thunkability witness.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Tower where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.HLevel.Base
  using (Π-is-prop; Πi-is-prop; module diagonal; loops→is-set)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties
  using (is-prop→is-set; is-contr-×; prop-inhabited→is-contr)
open import Core.Equiv.Base using (is-contr-equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
```

## The positive hand

The coaction distributes over the positive composition — the
witness read at `var`, the axiom half this hand closes — and
associativity is a path in one fiber, which the embedding condition
makes a proposition.

```agda
module tower⁺ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁺ : framing⁻.is-composable⁺ G rx) where

  open framing⁻ G rx public

  _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁺ g = C⁺ f g .fst

  reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁺ g) ≡ composite⁺ f g
  reflect-⨾⁺ f g = C⁺ f g .snd

  coact-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z) (k : coterm z)
           → coact (f ⨾⁺ g) k ≡ coact f (coact g k)
  coact-⨾⁺ f g k i = k .fst , reflect-⨾⁺ f g i (var _ , k)

  module tri⁺ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z) where
    E : judgment w z
    E γ = reflect f (γ .fst , coact g (coact h (γ .snd)))

    a₁ a₂ : is-representable G E
    a₁ = (f ⨾⁺ g) ⨾⁺ h
       , reflect-⨾⁺ (f ⨾⁺ g) h
       ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact h (γ .snd)))
    a₂ = f ⨾⁺ (g ⨾⁺ h)
       , reflect-⨾⁺ f (g ⨾⁺ h)
       ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁺ g h (γ .snd) i))

    σ : a₁ ≡ a₂
    σ = S E a₁ a₂

  assoc⁺ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
         → (f ⨾⁺ g) ⨾⁺ h ≡ f ⨾⁺ (g ⨾⁺ h)
  assoc⁺ f g h = ap fst (tri⁺.σ f g h)
```

## The negative hand

The mirror: the action distributes over the negative composition,
the witness read at `covar`.

```agda
module tower⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁻ : framing⁺.is-composable⁻ G corx) where

  open framing⁺ G corx public

  _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁻ g = C⁻ f g .fst

  reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁻ g) ≡ composite⁻ f g
  reflect-⨾⁻ f g = C⁻ f g .snd

  act-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z) (t : term x)
         → act (f ⨾⁻ g) t ≡ act g (act f t)
  act-⨾⁻ f g t i = t .fst , reflect-⨾⁻ f g i (t , covar _)

  assoc⁻ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
         → (f ⨾⁻ g) ⨾⁻ h ≡ f ⨾⁻ (g ⨾⁻ h)
  assoc⁻ f g h = reflect-lc G S
    ( reflect-⨾⁻ (f ⨾⁻ g) h
    ∙ (λ i γ → reflect h (act-⨾⁻ f g (γ .fst) i , γ .snd))
    ∙ sym ( reflect-⨾⁻ f (g ⨾⁻ h)
          ∙ (λ i γ → reflect-⨾⁻ g h i (act f (γ .fst) , γ .snd)) ) )
```

## The hands under the opposite

The opposite exchanges the halves of an argument, so a positive cut
there is a negative cut here with its factors exchanged. The two
compositions agree on the nose. The two associators are built by
different routes — one projects a fiber path, the other cancels
`reflect` — and `reflect-lc-fiber` identifies the routes, leaving
the positive associator at the opposite as the negative associator
reversed. Any positive-hand theorem instantiated at the opposite
therefore reads as a negative-hand theorem here.

```agda
module op-tower {o h} (G : virtual-graph o h) (open virtual-graph G)
  (corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁻ : framing⁺.is-composable⁻ G corx)
  (open duality G corx corx) where

  open tower⁻ G corx S C⁻ public

  op-embed : reflect-is-embedding (opⱽ G)
  op-embed = op-embedding G S

  op-cut⁺ : framing⁻.is-composable⁺ (opⱽ G) corx
  op-cut⁺ = op-composable⁺ C⁻

  module op = tower⁺ (opⱽ G) corx op-embed op-cut⁺

  op-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z) → op._⨾⁺_ g f ≡ f ⨾⁻ g
  op-⨾⁺ f g = refl

  op-assoc⁺ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
            → op.assoc⁺ h g f ≡ sym (assoc⁻ f g h)
  op-assoc⁺ {w = w} {z = z} f g h =
      ap (ap fst)
        (is-prop→is-set (S E) a₂ a₁
          (ap sw (op.tri⁺.σ h g f)) (sym (S E a₁ a₂)))
    ∙ ap sym (sym route)
    where
      E : judgment w z
      E γ = reflect h (act g (act f (γ .fst)) , γ .snd)

      a₁ a₂ : is-representable G E
      a₁ = (f ⨾⁻ g) ⨾⁻ h
         , reflect-⨾⁻ (f ⨾⁻ g) h
         ∙ (λ i γ → reflect h (act-⨾⁻ f g (γ .fst) i , γ .snd))
      a₂ = f ⨾⁻ (g ⨾⁻ h)
         , reflect-⨾⁻ f (g ⨾⁻ h)
         ∙ (λ i γ → reflect-⨾⁻ g h i (act f (γ .fst) , γ .snd))

      sw : is-representable (opⱽ G) (op.tri⁺.E h g f) → is-representable G E
      sw a = a .fst , λ i γ → a .snd i (γ .snd , γ .fst)

      route : assoc⁻ f g h ≡ ap fst (S E a₁ a₂)
      route =
          ap (reflect-lc G S {m = (f ⨾⁻ g) ⨾⁻ h} {n = f ⨾⁻ (g ⨾⁻ h)})
             (Path.assoc (reflect-⨾⁻ (f ⨾⁻ g) h)
                         (λ i γ → reflect h (act-⨾⁻ f g (γ .fst) i , γ .snd))
                         (sym (a₂ .snd)))
        ∙ reflect-lc-fiber G S E a₁ a₂
```

## The two towers together

```agda
module tower {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower⁺ G rx S C⁺ public
  open tower⁻ G corx S C⁻ public
  open framing G rx corx
    using (own⁻; own⁺; is-natural⁻; is-natural⁺; is-naturalᴶ⁻; is-naturalᴶ⁺)

  lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  lc = reflect-lc G S
```

A three-factor word whose two junctions take different hands is well
formed, and the order of its junctions decides its law. Where they
run negative then positive, the two bracketings represent one
judgment — the leading edge acting on the term half, the trailing
edge coacting on the coterm half, the middle edge reflected — so
the embedding condition identifies them and the word is a theorem.

```agda
  module mixed {w x y z} (f : hom w x) (g : hom x y) (k : hom y z) where
    E : judgment w z
    E γ = reflect g (act f (γ .fst) , coact k (γ .snd))

    a₁ a₂ : is-representable G E
    a₁ = (f ⨾⁻ g) ⨾⁺ k
       , reflect-⨾⁺ (f ⨾⁻ g) k
       ∙ (λ i γ → reflect-⨾⁻ f g i (γ .fst , coact k (γ .snd)))
    a₂ = f ⨾⁻ (g ⨾⁺ k)
       , reflect-⨾⁻ f (g ⨾⁺ k)
       ∙ (λ i γ → reflect-⨾⁺ g k i (act f (γ .fst) , γ .snd))

    σ : a₁ ≡ a₂
    σ = S E a₁ a₂

  mixed-assoc : ∀ {w x y z} (f : hom w x) (g : hom x y) (k : hom y z)
              → (f ⨾⁻ g) ⨾⁺ k ≡ f ⨾⁻ (g ⨾⁺ k)
  mixed-assoc f g k = ap fst (mixed.σ f g k)
```

Where the junctions run positive then negative, the bracketings
share no judgment: one closes its first junction inside `act`, the
other its second inside `coact`. Whether such a triple associates is
a property of the triple, and its two universal closures — at the
edge that leads the word, and at the edge that trails it — are
thunkability and linearity.

```agda
  associates : ∀ {w x y z} → hom w x → hom x y → hom y z → Type h
  associates f g h = (f ⨾⁺ g) ⨾⁻ h ≡ f ⨾⁺ (g ⨾⁻ h)

  thunkable : ∀ {w x} → hom w x → Type (o ⊔ h)
  thunkable {x = x} f = ∀ {y z} (g : hom x y) (h : hom y z) → associates f g h

  linear : ∀ {y z} → hom y z → Type (o ⊔ h)
  linear {y = y} h = ∀ {w x} (f : hom w x) (g : hom x y) → associates f g h
```

## Collapse at the crossed pairings

A hand's crossed pairing meets that hand's other unit law at the
composite of the two half-twists, so the pairing and that law together
identify the framing. Each pairing is an instance of a near unit
law, and each second hypothesis is a far one; the modules that
derive those laws instantiate these.

```agda
  collapse⁺ : (∀ x → rx x ⨾⁺ corx x ≡ rx x)
            → (∀ {x y} (g : hom x y) → rx x ⨾⁺ g ≡ g)
            → ∀ x → rx x ≡ corx x
  collapse⁺ pair⁺ L x = sym (pair⁺ x) ∙ L (corx x)

  collapse⁻ : (∀ x → rx x ⨾⁻ corx x ≡ corx x)
            → (∀ {x y} (f : hom x y) → f ⨾⁻ corx y ≡ f)
            → ∀ x → rx x ≡ corx x
  collapse⁻ pair⁻ R x = sym (R (rx x)) ∙ pair⁻ x
```

Flanking an edge with the far half-twist and cutting the flanked edge
back gives the plain cut again, through `mixed-assoc` and that
hand's far unit law.

```agda
  cross⁻ : ∀ {x y} → hom x y → hom x y
  cross⁻ {y = y} f = f ⨾⁻ corx y

  cross⁺ : ∀ {x y} → hom x y → hom x y
  cross⁺ {x} g = rx x ⨾⁺ g

  cut⁻-cross : (∀ {x y} (g : hom x y) → corx x ⨾⁺ g ≡ g)
             → ∀ {x y z} (f : hom x y) (g : hom y z)
             → cross⁻ f ⨾⁺ g ≡ f ⨾⁻ g
  cut⁻-cross unitl⁺ {y = y} f g =
    mixed-assoc f (corx y) g ∙ ap (f ⨾⁻_) (unitl⁺ g)

  cut⁺-cross : (∀ {x y} (f : hom x y) → f ⨾⁻ rx y ≡ f)
             → ∀ {x y z} (f : hom x y) (g : hom y z)
             → f ⨾⁻ cross⁺ g ≡ f ⨾⁺ g
  cut⁺-cross unitr⁻ {y = y} f g =
    sym (mixed-assoc f (rx y) g) ∙ ap (_⨾⁺ g) (unitr⁻ f)
```

## Closure under the cuts

`thunkable` and `linear` close under both cuts. Each proof consumes
the three unconditional associativity theorems and the given
witnesses, nothing else. Two closures are one-sided: `linear-⨾⁺`
reads only its leading factor, and `thunkable-⨾⁻` only its trailing
factor.

```agda
  thunkable-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → thunkable f → thunkable g → thunkable (f ⨾⁺ g)
  thunkable-⨾⁺ f g tf tg k h =
    ap (_⨾⁻ h) (assoc⁺ f g k)
    ∙ tf (g ⨾⁺ k) h
    ∙ ap (f ⨾⁺_) (tg k h)
    ∙ sym (assoc⁺ f g (k ⨾⁻ h))

  thunkable-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
               → thunkable g → thunkable (f ⨾⁻ g)
  thunkable-⨾⁻ f g tg k h =
    ap (_⨾⁻ h) (mixed-assoc f g k)
    ∙ assoc⁻ f (g ⨾⁺ k) h
    ∙ ap (f ⨾⁻_) (tg k h)
    ∙ sym (mixed-assoc f g (k ⨾⁻ h))

  linear-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → linear f → linear (f ⨾⁺ g)
  linear-⨾⁺ f g lf k m =
    sym (mixed-assoc (k ⨾⁺ m) f g)
    ∙ ap (_⨾⁺ g) (lf k m)
    ∙ assoc⁺ k (m ⨾⁻ f) g
    ∙ ap (k ⨾⁺_) (mixed-assoc m f g)

  linear-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → linear f → linear g → linear (f ⨾⁻ g)
  linear-⨾⁻ f g lf lg k m =
    sym (assoc⁻ (k ⨾⁺ m) f g)
    ∙ ap (_⨾⁻ g) (lf k m)
    ∙ lg k (m ⨾⁻ f)
    ∙ ap (k ⨾⁺_) (assoc⁻ m f g)
```

## The coherence square of a thunkability witness

`compat` is the length-4 compatibility square for a thunkable edge:
the two resolutions of the blocked word inside `f ⨾⁺ g ⨾⁻ h ⨾⁺ k`
agree. The square consumes the witness at `(g , h)` and at
`(g , h ⨾⁺ k)`; its other three edges are tower theorems. Over hom
sets each `associates` cell lives in a set, so the closure is a
proposition and the square holds for every witness.

```agda
  compat : ∀ {w x y z v} {f : hom w x} (T : thunkable f)
         → hom x y → hom y z → hom z v → Type h
  compat {f = f} T g h k =
      ap (_⨾⁺ k) (T g h)
        ∙ (assoc⁺ f (g ⨾⁻ h) k ∙ ap (f ⨾⁺_) (mixed-assoc g h k))
    ≡ mixed-assoc (f ⨾⁺ g) h k ∙ T g (h ⨾⁺ k)

  coherent : ∀ {w x} (f : hom w x) → thunkable f → Type (o ⊔ h)
  coherent {x = x} f T =
    ∀ {y z v} (g : hom x y) (h : hom y z) (k : hom z v)
    → compat T g h k

  thunkable-is-prop : (∀ {x y} → is-set (hom x y))
                    → ∀ {w x} (f : hom w x) → is-prop (thunkable f)
  thunkable-is-prop hs f =
    Πi-is-prop λ _ → Πi-is-prop λ _ →
    Π-is-prop λ _ → Π-is-prop λ _ → hs _ _

  compat-over-sets : (∀ {x y} → is-set (hom x y))
                   → ∀ {w x y z v} {f : hom w x} (T : thunkable f)
                     (g : hom x y) (h : hom y z) (k : hom z v)
                   → compat T g h k
  compat-over-sets hs T g h k = hs _ _ _ _
```

## The four flanking operations

Flanking an edge with a half-twist is a composite in one hand, and each
half-twist keeps one hand: `rx` the negative, `corx` the positive. `P` and
`Q` take the near side of their hand, where the leading half-twist meets
the negative cut and the trailing one the positive. `P'` and `Q'` take
the far side. All four are endofunctions of one edge type.

```agda
  module flanks where

    P : ∀ {x y} → hom x y → hom x y
    P {x} m = rx x ⨾⁻ m

    Q : ∀ {x y} → hom x y → hom x y
    Q {y = y} n = n ⨾⁺ corx y

    P' : ∀ {x y} → hom x y → hom x y
    P' {y = y} n = n ⨾⁻ rx y

    Q' : ∀ {x y} → hom x y → hom x y
    Q' {x} m = corx x ⨾⁺ m
```

Each unit law says that one flanking operation is the identity, and
the round law says that the composite of the two near flanks is. So
the five statements are five readings of the same four operations.

```agda
  unitl⁻-law unitr⁺-law unitr⁻-law unitl⁺-law round-law : Type (o ⊔ h)
  unitl⁻-law = ∀ {x y} (g : hom x y) → flanks.P g ≡ g
  unitr⁺-law = ∀ {x y} (f : hom x y) → flanks.Q f ≡ f
  unitr⁻-law = ∀ {x y} (f : hom x y) → flanks.P' f ≡ f
  unitl⁺-law = ∀ {x y} (g : hom x y) → flanks.Q' g ≡ g
  round-law  = ∀ {x y} (m : hom x y) → flanks.Q (flanks.P m) ≡ m
```

Naturality of a half-twist in its own hand equates the hand's two flanks.
Read at that half-twist, the negative equation is idempotence.

```agda
  nat⁻-law nat⁺-law idem⁻-law : Type (o ⊔ h)
  nat⁻-law  = ∀ {x y} (m : hom x y) → flanks.P m ≡ flanks.P' m
  nat⁺-law  = ∀ {x y} (m : hom x y) → flanks.Q' m ≡ flanks.Q m
  idem⁻-law = ∀ x → rx x ⨾⁻ rx x ≡ rx x
```
