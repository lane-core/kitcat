A deductive system as a category with one operator. The presentation
data is a wild category, one endo-operator `cross` on its edges, a
second endo-edge family `pivot`, and three laws relating them — a
flat telescope of twelve parameters. From that data the carrier
returns with the reflection a flanked word, readback is a theorem of
the laws, and every tier fiber is inhabited with its edge forced;
what remains is `residue`, three propositionality demands, and hom
sets discharge all three. In the other direction the cancellation layer
satisfies every law: the category is the positive cut, the operator
is the negative cut against `corx`, the pivot is `rx`. Both
round trips are componentwise, and the dictionary at the end reads
`associates`, `thunkable`, `linear`, and polarity as commutation
defects of the operator.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Presentation where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Data.Sigma
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-hlevel; Σ-prop-path)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Degenerate.Readback
open import Bb.VirtualGraphs.Degenerate.Cancellation
```

## The presentation

```agda
module presentation {o h}
  (ob : Type o) (hom : ob → ob → Type h)
  (unit : (x : ob) → hom x x)
  (_⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z)
  (assoc : ∀ {w x y z} (f : hom w x) (g : hom x y) (k : hom y z)
         → (f ⨾ g) ⨾ k ≡ f ⨾ (g ⨾ k))
  (unitl : ∀ {x y} (f : hom x y) → unit x ⨾ f ≡ f)
  (unitr : ∀ {x y} (f : hom x y) → f ⨾ unit y ≡ f)
  (cross : ∀ {x y} → hom x y → hom x y)
  (pivot : (x : ob) → hom x x)
  (cross-pivot : (x : ob) → cross (pivot x) ≡ unit x)
  (pivot-unitr : ∀ {x y} (f : hom x y) → cross f ⨾ pivot y ≡ f)
  (cross-cut : ∀ {x y z} (f : hom x y) (g : hom y z)
             → cross (cross f ⨾ g) ≡ cross f ⨾ cross g)
  where
```

The pivot's left law is the cross law and one unit law. The
reflection is the flanked word: the operator runs on the term half,
the coterm half stays where it is, and readback is the word at the
axiom — with `pivot` in the `rx` role and `unit` in the
`corx` role.

```agda
  pivot-unitl : ∀ {x y} (f : hom x y) → cross (pivot x) ⨾ f ≡ f
  pivot-unitl {x} f = ap (_⨾ f) (cross-pivot x) ∙ unitl f

  graph : virtual-graph o h
  graph .virtual-graph.ob  = ob
  graph .virtual-graph.hom = hom
  graph .virtual-graph.reflect f γ = (cross (γ .fst .snd) ⨾ f) ⨾ (γ .snd .snd)

  open framing graph pivot unit
  open absorbing⁻ graph pivot
  open absorbing⁺ graph unit

  readback : readback-of
  readback {y = y} f = ap (_⨾ unit y) (pivot-unitl f) ∙ unitr f
```

Each cut's representative is a word the operator writes: the
positive cut is the category's composition, the negative cut that
composition after the operator. Neither witness needs a hypothesis.

```agda
  cut⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → virtual-graph.reflect graph (f ⨾ g) ≡ composite⁺ f g
  cut⁺ f g = funext λ γ →
      ap (_⨾ (γ .snd .snd)) (sym (assoc (cross (γ .fst .snd)) f g))
    ∙ assoc (cross (γ .fst .snd) ⨾ f) g (γ .snd .snd)
    ∙ ap ((cross (γ .fst .snd) ⨾ f) ⨾_)
         (sym (ap (_⨾ (γ .snd .snd)) (pivot-unitl g)))

  cut⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → virtual-graph.reflect graph (cross f ⨾ g) ≡ composite⁻ f g
  cut⁻ f g = funext λ γ →
      ap (_⨾ (γ .snd .snd)) (sym (assoc (cross (γ .fst .snd)) (cross f) g))
    ∙ ap (λ e → (e ⨾ g) ⨾ (γ .snd .snd)) (sym (cross-cut (γ .fst .snd) f))
    ∙ ap (λ e → (cross e ⨾ g) ⨾ (γ .snd .snd))
         (sym (unitr (cross (γ .fst .snd) ⨾ f)))

  composable⁺ : is-composable⁺
  composable⁺ f g = (f ⨾ g) , cut⁺ f g

  composable⁻ : is-composable⁻
  composable⁻ f g = (cross f ⨾ g) , cut⁻ f g
```

Each absorption fiber is inhabited by the other family.

```agda
  cancel⁻ : (x : ob) → coact-π {x} {x} (unit x) ≡ snd
  cancel⁻ x = funext λ γ →
    ap (_⨾ (γ .snd)) (pivot-unitl (unit x)) ∙ unitl (γ .snd)

  cancel⁺ : (x : ob) → act-π {x} {x} (pivot x) ≡ snd
  cancel⁺ x = funext λ t →
    unitr (cross (t .snd) ⨾ pivot x) ∙ pivot-unitr (t .snd)
```

Readback makes the reflection injective, so each fiber's edge is
forced, and the pivot is pinned by one law per family.

```agda
  reflect-injective
    : ∀ {x y} {m n : hom x y}
    → virtual-graph.reflect graph m ≡ virtual-graph.reflect graph n → m ≡ n
  reflect-injective {x} {y} {m} {n} p =
    sym (readback m) ∙ happly p (var x , covar y) ∙ readback n

  cut⁺-forced : ∀ {x y z} (f : hom x y) (g : hom y z)
                (w : is-representable graph (composite⁺ f g))
              → w .fst ≡ f ⨾ g
  cut⁺-forced f g w = reflect-injective (w .snd ∙ sym (cut⁺ f g))

  cut⁻-forced : ∀ {x y z} (f : hom x y) (g : hom y z)
                (w : is-representable graph (composite⁻ f g))
              → w .fst ≡ cross f ⨾ g
  cut⁻-forced f g w = reflect-injective (w .snd ∙ sym (cut⁻ f g))

  centre⁻-forced : (x : ob) (w : fiber (coact-π {x} {x}) snd)
                 → w .fst ≡ unit x
  centre⁻-forced x (e , p) =
      sym (pivot-unitl e)
    ∙ sym (unitr (cross (pivot x) ⨾ e))
    ∙ happly p (x , unit x)

  centre⁺-forced : (x : ob) (w : fiber (act-π {x} {x}) snd)
                 → w .fst ≡ pivot x
  centre⁺-forced x (e , p) =
      sym (pivot-unitl e)
    ∙ sym (unitr (cross (pivot x) ⨾ e))
    ∙ happly p (x , pivot x)

  pivot-forced : (p q : (x : ob) → hom x x)
               → (∀ x → cross (q x) ≡ unit x)
               → (∀ {x y} (f : hom x y) → cross f ⨾ p y ≡ f)
               → ∀ x → p x ≡ q x
  pivot-forced p q cq up x =
    sym (ap (_⨾ p x) (cq x) ∙ unitl (p x)) ∙ up (q x)
```

## The residue

Each tier asks one fiber to be contractible, and the fiber's edge is
forced already, so what remains at each tier is one propositionality
demand. Hom sets give all three; the residue is not an equation
between operator words.

```agda
  residue : Type (o ⊔ h)
  residue = reflect-is-embedding graph
          × ((x : ob) → is-prop (fiber (coact-π {x} {x}) snd))
          × ((x : ob) → is-prop (fiber (act-π {x} {x}) snd))

  hom-sets→embedding : (∀ {x y} → is-set (hom x y)) → reflect-is-embedding graph
  hom-sets→embedding hset = embedding-from-hom-sets hset
    (λ {_} {_} {m} {n} q → sym (readback m) ∙ q ∙ readback n)

  fiber⁻-is-prop : (∀ {x y} → is-set (hom x y)) → (x : ob)
                 → is-prop (fiber (coact-π {x} {x}) snd)
  fiber⁻-is-prop hset x w w' =
    Σ-prop-path (λ e → Π-is-hlevel 2 (λ _ → hset) (coact-π e) snd)
      (centre⁻-forced x w ∙ sym (centre⁻-forced x w'))

  fiber⁺-is-prop : (∀ {x y} → is-set (hom x y)) → (x : ob)
                 → is-prop (fiber (act-π {x} {x}) snd)
  fiber⁺-is-prop hset x w w' =
    Σ-prop-path (λ e → Π-is-hlevel 2 (λ _ → hset) (act-π e) snd)
      (centre⁺-forced x w ∙ sym (centre⁺-forced x w'))

  hom-sets→residue : (∀ {x y} → is-set (hom x y)) → residue
  hom-sets→residue hset =
    hom-sets→embedding hset , fiber⁻-is-prop hset , fiber⁺-is-prop hset
```

The residue returns the four tiers in their contractible forms.

```agda
  contr-cut⁺ : residue → ∀ {x y z} (f : hom x y) (g : hom y z)
             → is-contr (is-representable graph (composite⁺ f g))
  contr-cut⁺ r f g = prop-inhabited→is-contr (r .fst _) (composable⁺ f g)

  contr-cut⁻ : residue → ∀ {x y z} (f : hom x y) (g : hom y z)
             → is-contr (is-representable graph (composite⁻ f g))
  contr-cut⁻ r f g = prop-inhabited→is-contr (r .fst _) (composable⁻ f g)

  tier⁻ : residue → is-absorbing⁻
  tier⁻ r x = prop-inhabited→is-contr (r .snd .fst x) (unit x , cancel⁻ x)

  tier⁺ : residue → is-absorbing⁺
  tier⁺ r x = prop-inhabited→is-contr (r .snd .snd x) (pivot x , cancel⁺ x)
```

## The presentation reaches the cancellation layer

Every presentation law is a theorem of the cancellation layer:
`cross-pivot` is `pair⁻`, `pivot-unitr` is `cut⁻-cross` against
`unitr⁻`, and `cross-cut` is `cross⁻-cut⁺`. The opposite exchanges
the two operators on the nose.

```agda
module presented {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (cc⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (framing⁻.composite⁺ G rx f g)))
  (cc⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (framing⁺.composite⁻ G corx f g)))
  (R : framing.readback-of G rx corx)
  (T⁻ : absorbing⁻.is-absorbing⁻ G rx)
  (T⁺ : absorbing⁺.is-absorbing⁺ G corx)
  where

  C⁺ : framing⁻.is-composable⁺ G rx
  C⁺ f g = cc⁺ f g .center

  C⁻ : framing⁺.is-composable⁻ G corx
  C⁻ f g = cc⁻ f g .center

  S : reflect-is-embedding G
  S = contr-cut⁻.embedding-from-contr-cut⁻ G rx corx R cc⁻

  open collapse G rx corx S C⁺ C⁻ R T⁻ T⁺ public

  pivot-unitr : ∀ {x y} (f : hom x y) → cross⁻ f ⨾⁺ rx y ≡ f
  pivot-unitr f = cut⁻-cross f (rx _) ∙ unitr⁻ f
```

```agda
  Sᵛ : reflect-is-embedding (opⱽ G)
  Sᵛ = op-embedding G S

  open duality G rx corx

  module op = collapse (opⱽ G) corx rx Sᵛ
    (op-composable⁺ C⁻) (op-composable⁻ C⁺) (op-readback R) T⁺ T⁻

  op-cross : ∀ {x y} (f : hom y x) → op.cross⁻ {x} {y} f ≡ cross⁺ f
  op-cross f = refl
```

Every reflection is a flanked word, so the presentation's reflection
agrees with the carrier's one edge at a time, and the graph round
trip closes outright. The readbacks share their endpoints, and
`readback-square` is the whole of what would identify them; nothing
here proves it and nothing here refutes it.

```agda
  reflect-word : ∀ {x y} (m : hom x y) (γ : argument x y)
               → reflect m γ ≡ ((γ .fst .snd) ⨾⁻ m) ⨾⁺ (γ .snd .snd)
  reflect-word m ((w , s) , (v , k)) =
      (λ i → reflect m ((w , R s (~ i)) , (v , k)))
    ∙ sym (happly (reflect-⨾⁻ s m) (var w , (v , k)))
    ∙ ⨾⁺-is-coact (s ⨾⁻ m) k

  back : virtual-graph o h
  back = presentation.graph ob hom corx _⨾⁺_ assoc⁺ unitl⁺ unitr⁺
           cross⁻ rx pair⁻ pivot-unitr cross⁻-cut⁺

  round-reflect : ∀ {x y} (m : hom x y) (γ : argument x y)
                → virtual-graph.reflect back m γ ≡ reflect m γ
  round-reflect m γ =
      ap (_⨾⁺ (γ .snd .snd)) (cut⁻-cross (γ .fst .snd) m)
    ∙ sym (reflect-word m γ)

  round-graph : back ≡ G
  round-graph i .virtual-graph.ob = ob
  round-graph i .virtual-graph.hom = hom
  round-graph i .virtual-graph.reflect m γ = round-reflect m γ i

  Rᵇ : framing.readback-of back rx corx
  Rᵇ = presentation.readback ob hom corx _⨾⁺_ assoc⁺ unitl⁺ unitr⁺
         cross⁻ rx pair⁻ pivot-unitr cross⁻-cut⁺

  readback-square : Type (o ⊔ h)
  readback-square = ∀ {x y} (f : hom x y)
                  → PathP (λ i → round-reflect f (var x , covar y) i ≡ f)
                          (Rᵇ f) (R f)

  round-readback
    : readback-square
    → PathP (λ i → framing.readback-of (round-graph i) rx corx) Rᵇ R
  round-readback sq i f = sq f i
```

## The dictionary

Each polarity notion is a commutation defect of the operator:
`associates f g h` says right multiplication by `h` erases the
defect between `cross⁻ (f ⨾⁺ g)` and `f ⨾⁺ cross⁻ g`, `thunkable`
erases it outright one trailing edge at a time, `linear` erases it
by right multiplication at every pair, and either polarity of an
object is representability of the operator on the edges into it.

```agda
  associates→cross : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
                   → associates f g h
                   → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h
  associates→cross f g h a =
      cut⁻-cross (f ⨾⁺ g) h
    ∙ a
    ∙ ap (f ⨾⁺_) (sym (cut⁻-cross g h))
    ∙ sym (assoc⁺ f (cross⁻ g) h)

  cross→associates : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
                   → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h
                   → associates f g h
  cross→associates f g h e =
      sym (cut⁻-cross (f ⨾⁺ g) h)
    ∙ e
    ∙ assoc⁺ f (cross⁻ g) h
    ∙ ap (f ⨾⁺_) (cut⁻-cross g h)

  thunkable→cross : ∀ {w x} (f : hom w x) → thunkable f
                  → ∀ {y} (g : hom x y) → cross⁻ (f ⨾⁺ g) ≡ f ⨾⁺ cross⁻ g
  thunkable→cross f T g =
      sym (unitr⁺ (cross⁻ (f ⨾⁺ g)))
    ∙ associates→cross f g (corx _) (T g (corx _))
    ∙ unitr⁺ (f ⨾⁺ cross⁻ g)

  cross→thunkable : ∀ {w x} (f : hom w x)
                  → (∀ {y} (g : hom x y) → cross⁻ (f ⨾⁺ g) ≡ f ⨾⁺ cross⁻ g)
                  → thunkable f
  cross→thunkable f e g h = cross→associates f g h (ap (_⨾⁺ h) (e g))

  linear→cross : ∀ {y z} (h : hom y z) → linear h
               → ∀ {w x} (f : hom w x) (g : hom x y)
               → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h
  linear→cross h L f g = associates→cross f g h (L f g)

  cross→linear : ∀ {y z} (h : hom y z)
               → (∀ {w x} (f : hom w x) (g : hom x y)
                  → cross⁻ (f ⨾⁺ g) ⨾⁺ h ≡ (f ⨾⁺ cross⁻ g) ⨾⁺ h)
               → linear h
  cross→linear h e f g = cross→associates f g h (e f g)

  represents : ob → Type (o ⊔ h)
  represents x = ∀ {w} (f : hom w x) → cross⁻ f ≡ f ⨾⁺ cross⁻ (corx x)

  represents-forced : (x : ob) (e : hom x x)
                    → (∀ {w} (f : hom w x) → cross⁻ f ≡ f ⨾⁺ e)
                    → e ≡ cross⁻ (corx x)
  represents-forced x e rep = sym (unitl⁺ e) ∙ sym (rep (corx x))

  linear-half-twist→represents : (x : ob) → linear (corx x) → represents x
  linear-half-twist→represents x L f = from-linear.cross⁻-into L f

  represents→linear-half-twist : (x : ob) → represents x → linear (corx x)
  represents→linear-half-twist x rep f g =
    cross→associates f g (corx x)
      (ap (_⨾⁺ corx x)
        ( rep (f ⨾⁺ g)
        ∙ assoc⁺ f g (cross⁻ (corx x))
        ∙ ap (f ⨾⁺_) (sym (rep g)) ))

  positive→represents : (x : ob) → positive x → represents x
  positive→represents x P = linear-half-twist→represents x (P x (corx x))

  represents→positive : (x : ob) → represents x → positive x
  represents→positive x rep =
    positive-of-corx x (represents→linear-half-twist x rep)

  negative→represents : (x : ob) → negative x → represents x
  negative→represents x N = positive→represents x (negative→positive x N)

  represents→negative : (x : ob) → represents x → negative x
  represents→negative x rep = positive→negative x (represents→positive x rep)
```

## The presentation round trip

The category component, the unit, and the pivot return on the nose;
the operator returns up to `unitr`, since the rebuilt negative cut
ends at the unit.

```agda
module round {o h}
  (ob : Type o) (hom : ob → ob → Type h)
  (unit : (x : ob) → hom x x)
  (_⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z)
  (assoc : ∀ {w x y z} (f : hom w x) (g : hom x y) (k : hom y z)
         → (f ⨾ g) ⨾ k ≡ f ⨾ (g ⨾ k))
  (unitl : ∀ {x y} (f : hom x y) → unit x ⨾ f ≡ f)
  (unitr : ∀ {x y} (f : hom x y) → f ⨾ unit y ≡ f)
  (cross : ∀ {x y} → hom x y → hom x y)
  (pivot : (x : ob) → hom x x)
  (cross-pivot : (x : ob) → cross (pivot x) ≡ unit x)
  (pivot-unitr : ∀ {x y} (f : hom x y) → cross f ⨾ pivot y ≡ f)
  (cross-cut : ∀ {x y z} (f : hom x y) (g : hom y z)
             → cross (cross f ⨾ g) ≡ cross f ⨾ cross g)
  (r : presentation.residue ob hom unit _⨾_ assoc unitl unitr
         cross pivot cross-pivot pivot-unitr cross-cut)
  where

  open presentation ob hom unit _⨾_ assoc unitl unitr
    cross pivot cross-pivot pivot-unitr cross-cut

  open presented graph pivot unit (contr-cut⁺ r) (contr-cut⁻ r) readback
    (tier⁻ r) (tier⁺ r)
    using (cross⁻; _⨾⁺_)

  round-cut : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁺ g ≡ f ⨾ g
  round-cut f g = refl

  round-cross : ∀ {x y} (f : hom x y) → cross⁻ f ≡ cross f
  round-cross f = unitr (cross f)
```
