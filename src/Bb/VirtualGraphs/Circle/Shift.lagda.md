Retuning the readback of the circle model — replacing the unit witness
`rb₀` with its winding shift `rb₁`, while the carrier, both half-twists,
and both cuts stay fixed — moves two of the presentation's laws by one
winding each and leaves the rest on the nose. The reflection square
between a graph and the graph of its own presentation is unmoved by
the retuning: it transfers between the two readback witnesses in both
directions, and at the circle model it reduces, at the axiom, to the
triviality of the mixed associator.

This module uses `--cubical`: it consumes `loop-nontrivial` and
`Circle-is-groupoid` in unerased positions, which ride the winding
equivalence `ua` builds.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Shift where

open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_; module Path)
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥)
open import Core.Path.Base using (ap-retr)
open import Core.Transport.J using (J)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-prop→is-set; sq-from-∙)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Presentation
open import Bb.VirtualGraphs.Circle.Model
open import Bb.VirtualGraphs.Circle.Torsor using (rb₀; rb₁)

open import HData.Circle
open Circle

open framing circle.model (λ _ → base) (λ _ → base) using (readback-of)
```

## The two readback witnesses

On the minimal carrier there is no readback field to retune:
`circle.model` is the one carrier, both half-twists fixed at `base`, and
`rb₀`/`rb₁` are its two readback witnesses, passed explicitly to
`presented` wherever a construction reads one.

```agda
R₀ R₁ : readback-of
R₀ = rb₀
R₁ = rb₁

readbacks-differ : ((f : Circle) → R₀ f ≡ R₁ f) → ⊥
readbacks-differ q =
  loop-nontrivial (sym (Path.unitl loop) ∙ sym (q base))
```

## The two presentations

```agda
module p₀ = presented circle.model (λ _ → base) (λ _ → base)
              circle.cc⁺ circle.cc⁻ R₀ circle.T⁻ circle.T⁺
module p₁ = presented circle.model (λ _ → base) (λ _ → base)
              circle.cc⁺ circle.cc⁻ R₁ circle.T⁻ circle.T⁺
```

The object, the hom family, the unit (`corx`), and the pivot
(`rx`) are the shared parameters of both instantiations outright,
not derived quantities with two occurrences to compare. The
composition and the operator are derived from the shared cuts alone,
so they return on the nose too.

```agda
same-cut : (f g : Circle) → p₀._⨾⁺_ f g ≡ p₁._⨾⁺_ f g
same-cut f g = refl

same-cross : (f : Circle) → p₀.cross⁻ f ≡ p₁.cross⁻ f
same-cross f = refl
```

`assoc` runs through the embedding condition. Its fiber is a
proposition, hence a set, so the two associators agree.

```agda
same-assoc : (f g k : Circle)
           → p₀.assoc⁺ f g k ≡ p₁.assoc⁺ f g k
same-assoc f g k = ap (ap fst)
  (is-prop→is-set (p₀.S (p₀.tri⁺.E f g k)) _ _
    (p₀.tri⁺.σ f g k) (p₁.tri⁺.σ f g k))
```

## The loop space at the axiom

Both half-twists sit at `base` and both cuts are the multiplication, so
every word the round trip writes at the axiom is a loop at `base`.
Every self-path family is central, and `conj` writes each loop as one
such family, so this loop space is commutative. `∙-from-sq` inverts
`sq-from-∙`: a square over the reflection path is a composite.

```agda
Ω : Type
Ω = base ≡ base

M : Circle → Circle
M t = mult t base

ap-M : (r : Ω) → ap M r ≡ r
ap-M r = ap-retr mult-unit-r r ∙ Path.unitl (r ∙ refl) ∙ Path.unitr r

central : ∀ {u} {A : Type u} (l : (x : A) → x ≡ x) {x y : A} (p : x ≡ y)
        → l x ∙ p ≡ p ∙ l y
central l {x} = J (λ y q → l x ∙ q ≡ q ∙ l y)
  (Path.unitr (l x) ∙ sym (Path.unitl (l x)))

comm : (a b : Ω) → a ∙ b ≡ b ∙ a
comm a b =
    ap (_∙ b) (sym (ap-M a))
  ∙ central (λ x → ap (λ k → mult k x) a) b
  ∙ ap (b ∙_) (ap-M a)

ω-cancel : (a b : Ω) → sym a ∙ (b ∙ a) ≡ b
ω-cancel a b = ap (sym a ∙_) (comm b a) ∙ Path.lc a b

ω-cancelr : {a b : Ω} (κ : Ω) → a ∙ κ ≡ b ∙ κ → a ≡ b
ω-cancelr {a} {b} κ h = sym (Path.rc κ a) ∙ ap (_∙ sym κ) h ∙ Path.rc κ b

ω-cancell : {p q : Ω} (a : Ω) → a ∙ p ≡ a ∙ q → p ≡ q
ω-cancell {p} {q} a h = sym (Path.lc a p) ∙ ap (sym a ∙_) h ∙ Path.lc a q

bump : (x α y β : Ω) → (x ∙ α) ∙ (y ∙ β) ≡ (x ∙ y) ∙ (α ∙ β)
bump x α y β =
    sym (Path.assoc x α (y ∙ β))
  ∙ ap (x ∙_)
      ( Path.assoc α y β
      ∙ ap (_∙ β) (comm α y)
      ∙ sym (Path.assoc y α β) )
  ∙ Path.assoc x y (α ∙ β)

∙-from-sq : ∀ {u} {A : Type u} {a b y : A} (q : a ≡ b) (p : a ≡ y) (r : b ≡ y)
          → PathP (λ i → q i ≡ y) p r → p ≡ q ∙ r
∙-from-sq {a = a} {y = y} =
  J (λ b' q' → (p : a ≡ y) (r : b' ≡ y) → PathP (λ i → q' i ≡ y) p r → p ≡ q' ∙ r)
    (λ p r h → h ∙ sym (Path.unitl r))
```

## The words at the axiom

`Cn` and `Cp` are the two cut witnesses read at the axiom, and neither
reads the readback. The remaining names are the words the two round
trips write there. Each one lands in `Ω`.

```agda
ax : virtual-graph.argument circle.model tt tt
ax = (tt , base) , (tt , base)

Cn Cp : Ω
Cn = λ i → p₀.C⁻ base base .snd i ax
Cp = λ i → p₀.C⁺ base base .snd i ax

pr₀ pr₁ ur₀ ur₁ ma₀ ma₁ rw₀ rw₁ ul₀ ul₁ dr₀ dr₁ rr₀ rr₁ : Ω
pr₀ = p₀.pair⁻ tt
pr₁ = p₁.pair⁻ tt
ur₀ = p₀.unitr⁺ base
ur₁ = p₁.unitr⁺ base
ma₀ = p₀.mixed-assoc base base base
ma₁ = p₁.mixed-assoc base base base
rw₀ = p₀.reflect-word base ax
rw₁ = p₁.reflect-word base ax
ul₀ = p₀.unitl⁺ base
ul₁ = p₁.unitl⁺ base
dr₀ = p₀.Rᵇ base
dr₁ = p₁.Rᵇ base
rr₀ = p₀.round-reflect base ax
rr₁ = p₁.round-reflect base ax
```

## One winding, four times

Each unit word spends the readback three times, twice forward and once
backward, so it gains one winding. The flanked word spends it twice
forward and once backward under an inverse, so it loses one. The
embedding condition carries the mixed associator, which therefore
does not move. `κ₀` is
the shift of the positive hand's left unit law, named and not computed.

```agda
sym-∙ : ∀ {u} {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → sym (p ∙ q) ≡ sym q ∙ sym p
sym-∙ p = J (λ _ q' → sym (p ∙ q') ≡ sym q' ∙ sym p)
  (ap sym (Path.unitr p) ∙ sym (Path.unitl (sym p)))

u : Ω
u = rb₁ base

e : u ≡ loop
e = Path.unitl loop

ap-M-u : ap M u ≡ loop
ap-M-u = ap (ap M) e ∙ ap-M loop

shape : (c a b : Ω) → a ≡ loop → b ≡ loop → sym a ∙ (c ∙ (b ∙ a)) ≡ c ∙ loop
shape c a b ea eb =
    ap (λ z → sym z ∙ (c ∙ (b ∙ z))) ea
  ∙ ap (λ z → sym loop ∙ (c ∙ (z ∙ loop))) eb
  ∙ ap (sym loop ∙_) (Path.assoc c loop loop)
  ∙ ω-cancel loop (c ∙ loop)

shape-refl : (c : Ω) → refl ∙ (c ∙ (refl ∙ refl)) ≡ c
shape-refl c = Path.unitl (c ∙ (refl ∙ refl))
             ∙ ap (c ∙_) (Path.unitl refl)
             ∙ Path.unitr c

pair-base : pr₀ ≡ Cn
pair-base = shape-refl Cn

pair-loop : pr₁ ≡ Cn ∙ loop
pair-loop = shape Cn u (ap M u) e ap-M-u

pair-shift : pr₁ ≡ pr₀ ∙ loop
pair-shift = pair-loop ∙ ap (_∙ loop) (sym pair-base)

unitr-base : ur₀ ≡ Cp
unitr-base = shape-refl Cp

unitr-loop : ur₁ ≡ Cp ∙ loop
unitr-loop = shape Cp u u e e

unitr-shift : ur₁ ≡ ur₀ ∙ loop
unitr-shift = unitr-loop ∙ ap (_∙ loop) (sym unitr-base)

word-base : rw₀ ≡ sym Cn ∙ sym Cp
word-base = Path.unitl (sym Cn ∙ (refl ∙ (sym Cp ∙ refl)))
          ∙ ap (sym Cn ∙_) (Path.unitl (sym Cp ∙ refl) ∙ Path.unitr (sym Cp))

word-loop : rw₁ ≡ (sym Cn ∙ sym Cp) ∙ sym loop
word-loop =
    ap (λ z → sym z ∙ (sym Cn ∙ (sym u ∙ (sym Cp ∙ u)))) ap-M-u
  ∙ ap (λ z → sym loop ∙ (sym Cn ∙ (sym z ∙ (sym Cp ∙ z)))) e
  ∙ ap (λ z → sym loop ∙ (sym Cn ∙ z)) (ω-cancel loop (sym Cp))
  ∙ comm (sym loop) (sym Cn ∙ sym Cp)

word-shift : rw₁ ≡ rw₀ ∙ sym loop
word-shift = word-loop ∙ ap (_∙ sym loop) (sym word-base)

sym-word-shift : sym rw₁ ≡ sym rw₀ ∙ loop
sym-word-shift =
  ap sym word-shift ∙ sym-∙ rw₀ (sym loop) ∙ comm loop (sym rw₀)

mixed-same : ma₁ ≡ ma₀
mixed-same = ap (ap fst)
  (is-prop→is-set (p₀.S (p₀.mixed.E base base base)) _ _
    (p₁.mixed.σ base base base) (p₀.mixed.σ base base base))

κ₀ κ : Ω
κ₀ = sym ul₀ ∙ ul₁
κ = (κ₀ ∙ loop) ∙ loop

unitl-shift : ul₁ ≡ ul₀ ∙ κ₀
unitl-shift = sym (Path.lc (sym ul₀) ul₁)

rb-shift : rb₁ base ≡ rb₀ base ∙ loop
rb-shift = refl
```

## Two law fields move

`cross-pivot` is the negative left unit law at the two half-twists —
`pair⁻` under the presentation's naming — and `unitr` is the positive
right unit law. Each gains one winding, so neither returns.

```agda
cross-pivot-shift : p₁.pair⁻ tt ≡ p₀.pair⁻ tt ∙ loop
cross-pivot-shift = pair-shift

unitr-field-shift : p₁.unitr⁺ base ≡ p₀.unitr⁺ base ∙ loop
unitr-field-shift = unitr-shift

cross-pivot-differs : p₁.pair⁻ tt ≡ p₀.pair⁻ tt → ⊥
cross-pivot-differs q = loop-nontrivial
  (ω-cancell pr₀ (sym pair-shift ∙ q ∙ sym (Path.unitr pr₀)))

unitr-field-differs : p₁.unitr⁺ base ≡ p₀.unitr⁺ base → ⊥
unitr-field-differs q = loop-nontrivial
  (ω-cancell ur₀ (sym unitr-shift ∙ q ∙ sym (Path.unitr ur₀)))
```

## The presentation and the readback shift together

The derived readback is the flanked word of the presentation read at
the axiom. It gains `κ₀` and two windings. The reflection square
against the field gains the same, so the shift cancels on both sides.

```agda
derived-form : (pr ul ur : Ω) → ap M (ap M pr ∙ ul) ∙ ur ≡ (pr ∙ ul) ∙ ur
derived-form pr ul ur =
  ap (_∙ ur) (ap-M (ap M pr ∙ ul) ∙ ap (_∙ ul) (ap-M pr))

round-form : (ma ul rw : Ω) → ap M (ma ∙ ul) ∙ sym rw ≡ (ma ∙ ul) ∙ sym rw
round-form ma ul rw = ap (_∙ sym rw) (ap-M (ma ∙ ul))

derived-shift : dr₁ ≡ dr₀ ∙ κ
derived-shift =
    derived-form pr₁ ul₁ ur₁
  ∙ ap (λ z → (z ∙ ul₁) ∙ ur₁) pair-shift
  ∙ ap (λ z → ((pr₀ ∙ loop) ∙ z) ∙ ur₁) unitl-shift
  ∙ ap (λ z → ((pr₀ ∙ loop) ∙ (ul₀ ∙ κ₀)) ∙ z) unitr-shift
  ∙ ap (_∙ (ur₀ ∙ loop)) (bump pr₀ loop ul₀ κ₀)
  ∙ bump (pr₀ ∙ ul₀) (loop ∙ κ₀) ur₀ loop
  ∙ ap (λ z → ((pr₀ ∙ ul₀) ∙ ur₀) ∙ (z ∙ loop)) (comm loop κ₀)
  ∙ ap (_∙ κ) (sym (derived-form pr₀ ul₀ ur₀))

round-shift : rr₁ ∙ rb₁ base ≡ (rr₀ ∙ rb₀ base) ∙ κ
round-shift =
    ap (_∙ rb₁ base) (round-form ma₁ ul₁ rw₁)
  ∙ ap (λ z → ((z ∙ ul₁) ∙ sym rw₁) ∙ rb₁ base) mixed-same
  ∙ ap (λ z → ((ma₀ ∙ z) ∙ sym rw₁) ∙ rb₁ base) unitl-shift
  ∙ ap (λ z → ((ma₀ ∙ (ul₀ ∙ κ₀)) ∙ z) ∙ rb₁ base) sym-word-shift
  ∙ ap (λ z → (z ∙ (sym rw₀ ∙ loop)) ∙ (rb₀ base ∙ loop)) (Path.assoc ma₀ ul₀ κ₀)
  ∙ ap (_∙ (rb₀ base ∙ loop)) (bump (ma₀ ∙ ul₀) κ₀ (sym rw₀) loop)
  ∙ bump ((ma₀ ∙ ul₀) ∙ sym rw₀) (κ₀ ∙ loop) (rb₀ base) loop
  ∙ ap (λ z → z ∙ κ) (ap (_∙ rb₀ base) (sym (round-form ma₀ ul₀ rw₀)))
```

## The square transfers both ways

The square at an edge is a path between two paths in a groupoid, hence
a proposition. So circle induction carries it from the axiom to every
edge, and the common shift carries it across the retuning.

```agda
Q₀ Q₁ : Circle → Type
Q₀ f = p₀.Rᵇ f ≡ p₀.round-reflect f ax ∙ rb₀ f
Q₁ f = p₁.Rᵇ f ≡ p₁.round-reflect f ax ∙ rb₁ f

all₀ : Q₀ base → (f : Circle) → Q₀ f
all₀ s = ind Q₀ s (is-prop→PathP (λ i → Circle-is-groupoid _ _ _ _) s s)

all₁ : Q₁ base → (f : Circle) → Q₁ f
all₁ s = ind Q₁ s (is-prop→PathP (λ i → Circle-is-groupoid _ _ _ _) s s)

square→ : p₀.readback-square → p₁.readback-square
square→ sq f = sq-from-∙ (all₁ step f)
  where
  step : Q₁ base
  step = derived-shift
       ∙ ap (_∙ κ) (∙-from-sq _ _ _ (sq base))
       ∙ sym round-shift

square← : p₁.readback-square → p₀.readback-square
square← sq f = sq-from-∙ (all₀ step f)
  where
  step : Q₀ base
  step = ω-cancelr κ
    (sym derived-shift ∙ ∙-from-sq _ _ _ (sq base) ∙ round-shift)
```

## The square at the mixed associator

The two unit laws reduce to the two cut witnesses, and the flanked
word reduces to their joint inverse. The positive hand's left unit law
stands on both sides. Only the mixed associator survives.

```agda
X : Ω
X = (Cn ∙ ul₀) ∙ Cp

left-form : dr₀ ≡ X
left-form = derived-form pr₀ ul₀ ur₀
          ∙ ap (λ z → (z ∙ ul₀) ∙ ur₀) pair-base
          ∙ ap ((Cn ∙ ul₀) ∙_) unitr-base

right-form : rr₀ ∙ rb₀ base ≡ X ∙ ma₀
right-form =
    ap (_∙ rb₀ base) (round-form ma₀ ul₀ rw₀)
  ∙ Path.unitr ((ma₀ ∙ ul₀) ∙ sym rw₀)
  ∙ ap ((ma₀ ∙ ul₀) ∙_)
      (ap sym word-base ∙ sym-∙ (sym Cn) (sym Cp) ∙ comm Cp Cn)
  ∙ bump ma₀ ul₀ Cn Cp
  ∙ ap (_∙ (ul₀ ∙ Cp)) (comm ma₀ Cn)
  ∙ bump Cn ma₀ ul₀ Cp
  ∙ ap ((Cn ∙ ul₀) ∙_) (comm ma₀ Cp)
  ∙ Path.assoc (Cn ∙ ul₀) Cp ma₀

square→mixed : Q₀ base → ma₀ ≡ refl
square→mixed h =
  sym (ω-cancell X (Path.unitr X ∙ (sym left-form ∙ h ∙ right-form)))

mixed→square : ma₀ ≡ refl → Q₀ base
mixed→square q =
  left-form ∙ sym (Path.unitr X) ∙ ap (X ∙_) (sym q) ∙ sym right-form
```

## The mixed associator is trivial at the axiom

The model reads the positive cut witness through `mult-assoc base`,
which is `refl`, so that witness degenerates at the axiom. The two
points of the mixed fiber then differ by unit laws alone. The fiber is
a set, so the associator's trace on the edges is `refl`.

```agda
mixed-base : ma₀ ≡ refl
mixed-base = ap (ap fst)
  (is-prop→is-set (p₀.S (p₀.mixed.E base base base)) _ _
    (p₀.mixed.σ base base base) (λ i → base , edge i))
  where
  edge : p₀.mixed.a₁ base base base .snd ≡ p₀.mixed.a₂ base base base .snd
  edge = Path.unitl (p₀.C⁻ base base .snd)
       ∙ sym (Path.unitr (p₀.C⁻ base base .snd))
```

## The square holds, at both readbacks

The minimal carrier has no readback field for `back` and the model to
disagree on, so the graph round trip closes unconditionally:
`round-graph` needs no hypothesis. What the square supplies instead is
the identification of the two readbacks themselves — `round-readback`
turns it into a `PathP` between the derived readback and the field,
lying over `round-graph`. The homs are the circle, which is not a set,
so neither square is free.

```agda
square₀ : p₀.readback-square
square₀ f = sq-from-∙ (all₀ (mixed→square mixed-base) f)

square₁ : p₁.readback-square
square₁ = square→ square₀

graph-returns₀ : p₀.back ≡ circle.model
graph-returns₀ = p₀.round-graph

graph-returns₁ : p₁.back ≡ circle.model
graph-returns₁ = p₁.round-graph

round-readback₀
  : PathP (λ i → framing.readback-of (p₀.round-graph i) (λ _ → base) (λ _ → base))
          p₀.Rᵇ R₀
round-readback₀ = p₀.round-readback square₀

round-readback₁
  : PathP (λ i → framing.readback-of (p₁.round-graph i) (λ _ → base) (λ _ → base))
          p₁.Rᵇ R₁
round-readback₁ = p₁.round-readback square₁
```

So the readback shift moves two of the presentation's derived laws —
`cross-pivot` and `unitr` — by one winding each, while its carrier,
its composition, and its operator return on the nose, and its
associator returns up to the path the embedding condition
supplies. The reflection square between a graph and the graph of
its own presentation transfers across the shift undisturbed: the
derived readback and the square against the field gain the same
combination `κ₀ ∙ loop ∙ loop`, named
here as `κ` and never computed further, and it cancels from both
sides. At the circle model the square reduces at the axiom to the
triviality of the mixed associator, which holds because `mult-assoc
base` is `refl` and the mixed fiber is a set — so the square holds at
both readback witnesses, with the homs left wild throughout: the
circle is a groupoid, not a set, and the argument spends exactly its
commutative loop space and the degeneracy of `mult-assoc` at `base`.
