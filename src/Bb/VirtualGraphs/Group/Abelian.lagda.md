An abelian group read as a one-object virtual graph, in its two framings.
The first holds a pair of elements, one for each hand, with every tier and
both cuts free at any such pair — outside the path-object regime, since a
fan here is the whole group. The second holds a single element and extracts
its hand's partner from the absorption tier alone; there the extraction
pins the partner to the held element's inverse, so the two-element freedom
of the first framing collapses to one.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Group.Abelian where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Equiv.Base using (_≃_; iso→equiv)
open import Core.HLevel.Base using (Π-is-hlevel; is-prop-equiv)
open import Core.Function.Embedding using (injective→is-embedding)
open import Core.Transport.Properties using (prop-inhabited→is-contr)

open import Core.Rx.Type
open import Core.Rx.Base

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Degenerate.Extraction
open import Bb.VirtualGraphs.Graph using (rxgraph)
```

## The group

Every construction below reads a single hypothesised abelian group: a
carrier, its operation, unit, and inverse, commutative and associative, with
one inverse law posited and the rest derived.

```agda
module _ {u} {A : Type u}
  (_·_ : A → A → A) (e : A) (inv : A → A)
  (A-set : is-set A)
  (assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  (comm  : ∀ a b → a · b ≡ b · a)
  (unitl : ∀ a → e · a ≡ a)
  (invl  : ∀ a → inv a · a ≡ e)
  where

  unitr : ∀ a → a · e ≡ a
  unitr a = comm a e ∙ unitl a

  invr : ∀ a → a · inv a ≡ e
  invr a = comm a (inv a) ∙ invl a

  cancel-l : ∀ a {b c} → a · b ≡ a · c → b ≡ c
  cancel-l a {b} {c} p =
    sym (unitl b)
    ∙ ap (_· b) (sym (invl a))
    ∙ assoc (inv a) a b
    ∙ ap (inv a ·_) p
    ∙ sym (assoc (inv a) a c)
    ∙ ap (_· c) (invl a)
    ∙ unitl c

  cancel-r : ∀ a {b c} → b · a ≡ c · a → b ≡ c
  cancel-r a {b} {c} p = cancel-l a (comm a b ∙ p ∙ comm c a)
```

## Framed on both hands

Framing the group at an arbitrary pair `t⁻ t⁺ : A` gives the carrier a
one-object virtual graph: the reflection reads an edge through the group
product, with each argument half contributing the factor its own side
supplies.

```agda
  module framed (t⁻ t⁺ : A) where

    VG : virtual-graph 0ℓ u
    VG .virtual-graph.ob          = ⊤
    VG .virtual-graph.hom _ _     = A
    VG .virtual-graph.reflect f γ = γ .fst .snd · (f · γ .snd .snd)

    open virtual-graph VG
    open framing⁻ VG (λ _ → t⁻)
    open framing⁺ VG (λ _ → t⁺)
    open absorbing⁻ VG (λ _ → t⁻)
    open absorbing⁺ VG (λ _ → t⁺)
    open framing VG (λ _ → t⁻) (λ _ → t⁺) using (cell⁻; cell⁺; embedding-from-hom-sets)
```

### The fans are the group

A fan at the one object is the group paired with it, so the graph is a path
object exactly when the group itself is a proposition.

```agda
    univalent→prop : rx.is-univalent (rxgraph VG (λ _ → t⁺)) → is-prop A
    univalent→prop univ = is-prop-equiv fan≃carrier (univ tt)
      where
      fan≃carrier : A ≃ rx.fan (rxgraph VG (λ _ → t⁺)) tt
      fan≃carrier = iso→equiv (λ a → tt , a) (λ z → z .snd) (λ _ → refl) (λ _ → refl)
```

### The embedding condition

Transmission surrounds an edge with one half-twist of each sign, and cancelling
them is injective, so the edges forming a set is the whole of the tier.

```agda
    transmit-injective : ∀ {m n : A} → t⁻ · (m · t⁺) ≡ t⁻ · (n · t⁺) → m ≡ n
    transmit-injective p = cancel-r t⁺ (cancel-l t⁻ p)

    stable : reflect-is-embedding VG
    stable = embedding-from-hom-sets (λ {_} {_} → A-set) transmit-injective
```

### Both cuts

Each composite judgment is a five-fold product with the half-twist of its own
sign at the junction, and reassociating gathers the middle three into one
edge.

```agda
    cut⁺ : A → A → A
    cut⁺ f k = f · (t⁻ · k)

    cut⁻ : A → A → A
    cut⁻ f k = (f · t⁺) · k

    composable⁺ : is-composable⁺
    composable⁺ f k = cut⁺ f k , funext λ γ →
      ap (γ .fst .snd ·_) (assoc f (t⁻ · k) (γ .snd .snd)
                           ∙ ap (f ·_) (assoc t⁻ k (γ .snd .snd)))

    composable⁻ : is-composable⁻
    composable⁻ f k = cut⁻ f k , funext λ γ →
      ap (γ .fst .snd ·_) (assoc (f · t⁺) k (γ .snd .snd))
      ∙ sym (assoc (γ .fst .snd) (f · t⁺) (k · (γ .snd .snd)))
```

### Both unit tiers

An action map holds the half it does not act on at that half's axiom, so it
multiplies by that half's half-twist: `coact-π` by the future's `t⁻`, `act-π` by
the buffer's `t⁺`. The edge acting as the second projection is therefore
that half-twist's inverse.

```agda
    coact-π-injective : ∀ {m n : A} → coact-π {tt} {tt} m ≡ coact-π {tt} {tt} n → m ≡ n
    coact-π-injective p = cancel-r e (cancel-l t⁻ (happly p (tt , e)))

    act-π-injective : ∀ {m n : A} → act-π {tt} {tt} m ≡ act-π {tt} {tt} n → m ≡ n
    act-π-injective p = cancel-r t⁺ (cancel-l e (happly p (tt , e)))

    unital⁻ : is-absorbing⁻
    unital⁻ x = prop-inhabited→is-contr
      (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set)
        (coact-π {tt} {tt}) coact-π-injective snd)
      ( inv t⁻
      , funext λ γ → sym (assoc t⁻ (inv t⁻) (γ .snd))
                   ∙ ap (_· γ .snd) (invr t⁻)
                   ∙ unitl (γ .snd) )

    unital⁺ : is-absorbing⁺
    unital⁺ x = prop-inhabited→is-contr
      (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set)
        (act-π {tt} {tt}) act-π-injective snd)
      ( inv t⁺
      , funext λ t → ap (t .snd ·_) (invl t⁺) ∙ unitr (t .snd) )
```

A hand's cell reads the opposite half's half-twist through the opposite half's
action, and each half-twist acting on its own family lands exactly there — both
sides multiplication by `t⁻ · t⁺`.

```agda
    pin⁻ : ∀ x → coact-π t⁺ ≡ cell⁻ x
    pin⁻ _ = funext λ γ →
      sym (assoc t⁻ t⁺ (γ .snd)) ∙ comm (t⁻ · t⁺) (γ .snd)

    pin⁺ : ∀ x → act-π t⁻ ≡ cell⁺ x
    pin⁺ _ = funext λ t → comm (t .snd) (t⁻ · t⁺) ∙ assoc t⁻ t⁺ (t .snd)
```

The composition hands themselves come from the two cut witnesses just built.

```agda
    open tower VG (λ _ → t⁻) (λ _ → t⁺) stable composable⁺ composable⁻
      using (_⨾⁺_; _⨾⁻_)
```

### The two boundaries, as arithmetic

The cancellation is that the two framing elements compose to the unit.

```agda
    cancels→ : t⁻ · t⁺ ≡ e → ∀ x → cell⁻ x ≡ snd
    cancels→ K _ = funext λ γ → ap (γ .snd ·_) K ∙ unitr (γ .snd)

    →cancels : (∀ x → cell⁻ x ≡ snd) → t⁻ · t⁺ ≡ e
    →cancels K = sym (unitl (t⁻ · t⁺)) ∙ happly (K tt) (tt , e)
```

Agreement of the two cuts is that the two framing elements are equal: the
cuts are the same product with the junction's half-twist differing by sign, so
their difference is the framing's.

```agda
    cuts-agree→ : t⁻ ≡ t⁺
                → ∀ {x y z} (f : hom x y) (k : hom y z)
                → composite⁺ f k ≡ composite⁻ f k
    cuts-agree→ T f k = funext λ γ →
      let a = γ .fst .snd ; b = γ .snd .snd in
        ap (λ s → a · (f · (s · (k · b)))) T
        ∙ ap (a ·_) (sym (assoc f t⁺ (k · b)))
        ∙ sym (assoc a (f · t⁺) (k · b))

    →cuts-agree : (∀ {x y z} (f : hom x y) (k : hom y z)
                   → composite⁺ f k ≡ composite⁻ f k)
                → t⁻ ≡ t⁺
    →cuts-agree X = sym red⁻ ∙ happly (X e e) ((tt , e) , (tt , e)) ∙ red⁺
      where
      red⁻ : e · (e · (t⁻ · (e · e))) ≡ t⁻
      red⁻ = unitl _ ∙ unitl _ ∙ ap (t⁻ ·_) (unitl e) ∙ unitr t⁻

      red⁺ : (e · (e · t⁺)) · (e · e) ≡ t⁺
      red⁺ = ap (_· (e · e)) (unitl _ ∙ unitl t⁺)
           ∙ ap (t⁺ ·_) (unitl e) ∙ unitr t⁺
```

So a framing whose two elements differ gives the graph two genuinely
distinct cuts, and one whose elements are mutually inverse gives the
cancelling case. Both together force each element to be its own inverse.

```agda
    both→ : t⁻ · t⁺ ≡ e → t⁻ ≡ t⁺ → t⁺ · t⁺ ≡ e
    both→ K T = ap (_· t⁺) (sym T) ∙ K
```

### What each hand's unit actually is

Each cut carries a junction half-twist, so the coterm hand's composition is the
product half-twisted by `t⁻` and its unit is that element's inverse.

```agda
    unit⁻-is-inverse : (u : A) → (∀ {x y} (f : hom x y) → f ⨾⁺ u ≡ f)
                     → t⁻ · u ≡ e
    unit⁻-is-inverse u U = sym (unitl (t⁻ · u)) ∙ U e

    unit⁺-is-inverse : (u : A) → (∀ {x y} (f : hom x y) → u ⨾⁻ f ≡ f)
                     → u · t⁺ ≡ e
    unit⁺-is-inverse u U = sym (unitr (u · t⁺)) ∙ U e
```

The composite of the two half-twists therefore carries three, and demanding it
be the unit is a cubic condition on the framing rather than the
cancellation.

```agda
    ι⁻ : A
    ι⁻ = t⁻ ⨾⁺ t⁺

    ι⁻-unit→cubic : (∀ {x y} (f : hom x y) → f ⨾⁺ ι⁻ ≡ f)
                  → t⁻ · (t⁻ · (t⁻ · t⁺)) ≡ e
    ι⁻-unit→cubic U = sym (unitl _) ∙ U e

    ι⁺ : A
    ι⁺ = t⁻ ⨾⁻ t⁺

    ι⁺-unit→cubic : (∀ {x y} (f : hom x y) → ι⁺ ⨾⁻ f ≡ f)
                  → (((t⁻ · t⁺) · t⁺) · t⁺) ≡ e
    ι⁺-unit→cubic U = sym (unitr _) ∙ U e
```

Read across the hands instead, the count comes out even: one hand's
composite of the two half-twists carries the *other* hand's junction, and is
that hand's unit exactly under the cancellation.

```agda
    ι⁻-unit⁺→square : (∀ {x y} (f : hom x y) → ι⁻ ⨾⁻ f ≡ f)
                    → (t⁻ · (t⁻ · t⁺)) · t⁺ ≡ e
    ι⁻-unit⁺→square U = sym (unitr _) ∙ U e

    cancels→ι⁻-unit⁺ : t⁻ · t⁺ ≡ e → ∀ {x y} (f : hom x y) → ι⁻ ⨾⁻ f ≡ f
    cancels→ι⁻-unit⁺ K f =
      ap (λ s → (s · t⁺) · f) (ap (t⁻ ·_) K ∙ unitr t⁻)
      ∙ ap (_· f) K
      ∙ unitl f
```

### The tier's centre against the framing

An edge whose coterm action is the projection is the held half-twist's inverse —
the centre `unital⁻` supplies — and under the cancellation that inverse is
the other half-twist again, so unit and framing coincide exactly there.

```agda
    absorber⁻-is-inverse : (u : A) → (∀ γ → coact-π {tt} {tt} u γ ≡ γ .snd) → t⁻ · u ≡ e
    absorber⁻-is-inverse u P = sym (ap (t⁻ ·_) (unitr u)) ∙ P (tt , e)

    absorber⁻-is-corx : t⁻ · t⁺ ≡ e
                        → (u : A) → (∀ γ → coact-π {tt} {tt} u γ ≡ γ .snd) → u ≡ t⁺
    absorber⁻-is-corx K u P = cancel-l t⁻ (absorber⁻-is-inverse u P ∙ sym K)
```

### What does unhalf-twist it

The half-twist enters because a cut fills one argument slot with an axiom half.
A two-payload string fills no slot — the factors sit adjacent — and it is
represented by the plain product.

```agda
    string : A → A → argument tt tt → A
    string f g γ = γ .fst .snd · (f · (g · γ .snd .snd))

    string-rep : (f g : A) → string f g ≡ reflect (f · g)
    string-rep f g = funext λ γ →
      ap (γ .fst .snd ·_) (sym (assoc f g (γ .snd .snd)))

    cut⁺-is-half-twisted : (f g : A) → cut⁺ f g ≡ f · (t⁻ · g)
    cut⁺-is-half-twisted _ _ = refl

    cut⁻-is-half-twisted : (f g : A) → cut⁻ f g ≡ (f · t⁺) · g
    cut⁻-is-half-twisted _ _ = refl
```

Against the plain product the composite of the two half-twists is the
cancellation itself, with no residue.

```agda
    string-half-twists : string t⁻ t⁺ ≡ reflect (t⁻ · t⁺)
    string-half-twists = string-rep t⁻ t⁺
```

### A candidate filler, and what it costs

Filling the junction with a candidate rather than with an axiom half. The
candidate is self-consistent when composing the two half-twists through it
returns it — and that condition is the cancellation, with no residue.

```agda
    cut[_] : A → A → A → A
    cut[ c ] f g = f · (c · g)

    self-consistent : A → Type u
    self-consistent c = cut[ c ] t⁻ t⁺ ≡ c

    self-consistent→cancels : (c : A) → self-consistent c → t⁻ · t⁺ ≡ e
    self-consistent→cancels c p = cancel-r c
      ( assoc t⁻ t⁺ c
      ∙ ap (t⁻ ·_) (comm t⁺ c)
      ∙ p
      ∙ sym (unitl c) )

    cancels→self-consistent : t⁻ · t⁺ ≡ e → (c : A) → self-consistent c
    cancels→self-consistent K c =
      ap (t⁻ ·_) (comm c t⁺)
      ∙ sym (assoc t⁻ t⁺ c)
      ∙ ap (_· c) K
      ∙ unitl c
```

## Framed on one hand, extracted

Framing the group at a single element `t⁻ : A` posits only the negative
tier; the positive half-twist is not chosen but extracted as that tier's centre.

```agda
  module one-half-twist (t⁻ : A) where

    cπ : A → Sigma ⊤ (λ _ → A) → A
    cπ m k = t⁻ · (m · k .snd)

    aπ : A → Sigma ⊤ (λ _ → A) → A
    aπ m t = t .snd · (m · inv t⁻)

    gf : A → Sigma ⊤ (λ _ → A) × Sigma ⊤ (λ _ → A) → A
    gf m γ = γ .fst .snd · (m · γ .snd .snd)

    cπ-inj : {m n : A} → cπ m ≡ cπ n → m ≡ n
    cπ-inj p = cancel-r e (cancel-l t⁻ (happly p (tt , e)))

    aπ-inj : {m n : A} → aπ m ≡ aπ n → m ≡ n
    aπ-inj p = cancel-r (inv t⁻) (cancel-l e (happly p (tt , e)))

    gf-inj : {m n : A} → gf m ≡ gf n → m ≡ n
    gf-inj p = cancel-r e (cancel-l e (happly p ((tt , e) , (tt , e))))

    absorb-wit : ∀ (k : Sigma ⊤ (λ _ → A)) → cπ (inv t⁻) k ≡ k .snd
    absorb-wit k =
      sym (assoc t⁻ (inv t⁻) (k .snd)) ∙ ap (_· k .snd) (invr t⁻) ∙ unitl (k .snd)

    tier⁻ : is-contr (fiber cπ snd)
    tier⁻ = prop-inhabited→is-contr
      (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set) cπ cπ-inj snd)
      (inv t⁻ , funext absorb-wit)

    tier⁺ : is-contr (fiber aπ snd)
    tier⁺ = prop-inhabited→is-contr
      (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set) aπ aπ-inj snd)
      ( inv (inv t⁻)
      , funext λ t → ap (t .snd ·_) (invl (inv t⁻)) ∙ unitr (t .snd) )

    GM : virtual-graph 0ℓ u
    GM .virtual-graph.ob          = ⊤
    GM .virtual-graph.hom _ _     = A
    GM .virtual-graph.reflect m γ = γ .fst .snd · (m · γ .snd .snd)

    S : reflect-is-embedding GM
    S = embedding-from-injective GM (λ {_} {_} → A-set) (λ {_} {_} → gf-inj)

    cut⁺ : framing⁻.is-composable⁺ GM (λ _ → t⁻)
    cut⁺ f g = f · (t⁻ · g) , funext λ γ →
      ap (γ .fst .snd ·_)
        (assoc f (t⁻ · g) (γ .snd .snd) ∙ ap (f ·_) (assoc t⁻ g (γ .snd .snd)))

    cut⁻ : framing⁺.is-composable⁻ GM (λ _ → inv t⁻)
    cut⁻ f g = (f · inv t⁻) · g , funext λ γ →
      ap (γ .fst .snd ·_) (assoc (f · inv t⁻) g (γ .snd .snd))
      ∙ sym (assoc (γ .fst .snd) (f · inv t⁻) (g · γ .snd .snd))
```

### The extraction, run at the model

The extraction telescope is inhabited entire, its positive half-twist pinned to
`inv t⁻`.

```agda
    open extraction GM (λ _ → t⁻) (λ _ → tier⁻)
    open extraction.system⁻ GM (λ _ → t⁻) (λ _ → tier⁻) S cut⁺ cut⁻ (λ _ → tier⁺)
```

Whatever proof the negative tier is given, its centre is the inverse of the
posited half-twist.

```agda
    corx-forced : (c : is-contr (fiber (coact-π {tt} {tt}) snd))
                  → c .center .fst ≡ inv t⁻
    corx-forced c = ap fst (c .paths (inv t⁻ , funext absorb-wit))
```

And the positive centre is the double inverse, so the term-side
cancellation holds at every element.

```agda
    inv-invol : ∀ a → inv (inv a) ≡ a
    inv-invol a = cancel-r (inv a) (invl (inv a) ∙ sym (invr a))

    group-agree : agree
    group-agree x = inv-invol t⁻

    group-cancel⁺ : cancel⁺
    group-cancel⁺ = agree→cancel⁺ group-agree
```
