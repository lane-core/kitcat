The per-object recognition shape. At each object a pair of endo-edges
stands in the axiom slot: `flanks` is the sandwich equation read at
that object's own edges, `inv⁻ᵗ` and `inv⁺ᵗ` are the two fibers
anchored at the pair, and `is-half-twist` is their conjunction. `is-framed`
asks each object for a pair carrying the condition. A family of pairs
is the same datum as a candidate, and readback crosses the two forms
definitionally, with `flanks` its diagonal fragment. Where the framing
a recognition witness supplies carries both cuts, the two
cancellations are the four absorption hypotheses of the tower, so the
recognized pair earns one unit law per hand.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Shape where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.HLevel.Base
  using (Π-is-prop; Πi-is-prop; is-prop-×; Σ-prop-path)
open import Core.Equiv.Base using (_≃_; iso→equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Degenerate.Tower
open import Bb.VirtualGraphs.Recognition
```

## The shape

A pair at an object is two endo-edges, the one filling the term half
first. The two action maps anchor at the pair, `flanks` is the
sandwich equation read at the object's own endo-edges, and the two
fibers ask each action map for a unique point over the second
projection.

```agda
module shape {o h} (G : virtual-graph o h) where
  open virtual-graph G

  pair : ob → Type h
  pair x = hom x x × hom x x

  coact-πᵗ : {x : ob} → pair x → hom x x → (γ : coterm x) → hom x (γ .fst)
  coact-πᵗ {x} p e γ = reflect e ((x , p .fst) , γ)

  act-πᵗ : {x : ob} → pair x → hom x x → (t : term x) → hom (t .fst) x
  act-πᵗ {x} p e t = reflect e (t , (x , p .snd))

  flanks : {x : ob} → pair x → Type h
  flanks {x} p = (f : hom x x) → reflect f ((x , p .fst) , (x , p .snd)) ≡ f

  inv⁻ᵗ inv⁺ᵗ : {x : ob} → pair x → Type (o ⊔ h)
  inv⁻ᵗ p = is-contr (fiber (coact-πᵗ p) snd)
  inv⁺ᵗ p = is-contr (fiber (act-πᵗ p) snd)

  is-half-twist : {x : ob} → pair x → Type (o ⊔ h)
  is-half-twist p = flanks p × (inv⁻ᵗ p × inv⁺ᵗ p)

  is-framed : Type (o ⊔ h)
  is-framed = (x : ob) → Σ p ∶ pair x , is-half-twist p
```

Each fiber clause is a proposition pointwise. The sandwich clause is
an equation between edges, so it is a proposition only where the homs
are.

```agda
  inv⁻ᵗ-is-prop : {x : ob} (p : pair x) → is-prop (inv⁻ᵗ p)
  inv⁻ᵗ-is-prop p = is-contr-is-prop _

  inv⁺ᵗ-is-prop : {x : ob} (p : pair x) → is-prop (inv⁺ᵗ p)
  inv⁺ᵗ-is-prop p = is-contr-is-prop _
```

## The family form

A candidate states the two families as a product. The family form
gathers the same data per object, and the two are related by the
distribution of Π over ×, a definitional isomorphism. Readback
crosses it by `refl`.

```agda
  family : Type (o ⊔ h)
  family = (x : ob) → pair x

  split : candidate.frame G ≃ family
  split = iso→equiv
    (λ p x → p .fst x , p .snd x)
    (λ P → (λ x → P x .fst) , (λ x → P x .snd))
    (λ _ → refl) (λ _ → refl)

  rbᶠ : family → Type (o ⊔ h)
  rbᶠ P = ∀ {x y} (f : hom x y)
        → reflect f ((x , P x .fst) , (y , P y .snd)) ≡ f

  rb-split : (p : candidate.frame G) → candidate.rb G p ≡ rbᶠ (split .fst p)
  rb-split p = refl
```

The instance of `rbᶠ` at `f : hom x y` reads `P x .fst` and `P y .snd`,
one component from each endpoint's pair. No condition on the pair at
one object states it. What survives pointwise is the diagonal, the
instances at the endo-edges, and `flanks` is that fragment.

```agda
  diag : (P : family) → rbᶠ P → (x : ob) → flanks (P x)
  diag P R x f = R f
```

## Recognition to cancellation

The sandwich equation forces each fiber point to the pair's own
component. With the contractible fibers this gives the two
cancellations: the second component closes every coterm at the
object, and the first component opens every term.

```agda
  point⁻ : {x : ob} (p : pair x) → flanks p
         → (w : fiber (coact-πᵗ p) snd) → w .fst ≡ p .snd
  point⁻ {x} p F w = sym (F (w .fst)) ∙ happly (w .snd) (x , p .snd)

  point⁺ : {x : ob} (p : pair x) → flanks p
         → (w : fiber (act-πᵗ p) snd) → w .fst ≡ p .fst
  point⁺ {x} p F w = sym (F (w .fst)) ∙ happly (w .snd) (x , p .fst)

  cancel⁻ : {x : ob} (p : pair x) → is-half-twist p → coact-πᵗ p (p .snd) ≡ snd
  cancel⁻ p (F , I⁻ , I⁺) =
    subst (λ e → coact-πᵗ p e ≡ snd) (point⁻ p F (I⁻ .center))
          (I⁻ .center .snd)

  cancel⁺ : {x : ob} (p : pair x) → is-half-twist p → act-πᵗ p (p .fst) ≡ snd
  cancel⁺ p (F , I⁻ , I⁺) =
    subst (λ e → act-πᵗ p e ≡ snd) (point⁺ p F (I⁺ .center))
          (I⁺ .center .snd)
```

## The cuts of a recognized framing

A family splits into the two half-twist families of the framed vocabulary,
and each cut composite at those families is the judgment-level
composite at the corresponding candidate, on the nose.

```agda
  rx-of corx-of : family → (x : ob) → hom x x
  rx-of P x = P x .fst
  corx-of P x = P x .snd

  ⊛⁺-form : (P : family) {x y z : ob} (f : hom x y) (g : hom y z)
          → framing⁻.composite⁺ G (rx-of P) f g
          ≡ clause._⊛⁺_ G (rx-of P , corx-of P) (reflect f) (reflect g)
  ⊛⁺-form P f g = refl

  ⊛⁻-form : (P : family) {x y z : ob} (f : hom x y) (g : hom y z)
          → framing⁺.composite⁻ G (corx-of P) f g
          ≡ clause._⊛⁻_ G (rx-of P , corx-of P) (reflect f) (reflect g)
  ⊛⁻-form P f g = refl
```

The cuts relative to a recognition witness are the two composability
conditions at the framing it supplies, each strengthened to
contractibility of the fiber. Together with the embedding condition
they make one type.

```agda
  frame-of : is-framed → family
  frame-of R x = R x .fst

  cuts : is-framed → Type (o ⊔ h)
  cuts R =
      ( ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (is-representable G
          (framing⁻.composite⁺ G (rx-of (frame-of R)) f g)) )
    × ( ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (is-representable G
          (framing⁺.composite⁻ G (corx-of (frame-of R)) f g)) )

  is-deductive-system-depreciated : Type (o ⊔ h)
  is-deductive-system-depreciated = reflect-is-embedding G × (Σ R ∶ is-framed , cuts R)
```

The cuts are contractibility conditions and the embedding condition
is a proposition, so the whole type is one wherever the framing
component is.

```agda
  cuts-is-prop : (R : is-framed) → is-prop (cuts R)
  cuts-is-prop R = is-prop-×
    ( Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
      Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _ )
    ( Πi-is-prop λ _ → Πi-is-prop λ _ → Πi-is-prop λ _ →
      Π-is-prop λ _ → Π-is-prop λ _ → is-contr-is-prop _ )

  deductive-prop : is-prop is-framed → is-prop is-deductive-system-depreciated
  deductive-prop W = is-prop-× (reflect-is-embedding-is-prop G) σ-prop
    where
      σ-prop : is-prop (Σ R ∶ is-framed , cuts R)
      σ-prop u v = Σ-prop-path cuts-is-prop (W (u .fst) (v .fst))
```

## The tower over a recognition witness

The framing a witness supplies has each cell trivial and each half-twist
pinned to the cell on its side — the four absorption hypotheses,
built from the two cancellations alone.

```agda
module recognized {o h} (G : virtual-graph o h) (R : shape.is-framed G) where
  open virtual-graph G
  open shape G
  open framing G (rx-of (frame-of R)) (corx-of (frame-of R))

  θ⁻ θ⁺ : (x : ob) → hom x x
  θ⁻ = rx-of (frame-of R)
  θ⁺ = corx-of (frame-of R)

  K⁻ᴿ : ∀ x → cell⁻ x ≡ snd
  K⁻ᴿ x = funext λ γ →
    happly (cancel⁺ (R (γ .fst) .fst) (R (γ .fst) .snd)) (x , γ .snd)

  K⁺ᴿ : ∀ x → cell⁺ x ≡ snd
  K⁺ᴿ x = funext λ t →
    happly (cancel⁻ (R (t .fst) .fst) (R (t .fst) .snd)) (x , t .snd)

  pin⁻ᴿ : ∀ x → coact-π (θ⁺ x) ≡ cell⁻ x
  pin⁻ᴿ x = cancel⁻ (R x .fst) (R x .snd) ∙ sym (K⁻ᴿ x)

  pin⁺ᴿ : ∀ x → act-π (θ⁻ x) ≡ cell⁺ x
  pin⁺ᴿ x = cancel⁺ (R x .fst) (R x .snd) ∙ sym (K⁺ᴿ x)
```

With the embedding condition and both cuts, the tower runs at this
framing and the four hypotheses give one unit law per hand: a right
unit for the positive hand at `θ⁺`, a left unit for the negative hand
at `θ⁻`. The four closure lemmas of the tower come with it, since
they consume the three associativity theorems and nothing else.

```agda
  module derived (S : reflect-is-embedding G)
    (C⁺ : framing⁻.is-composable⁺ G θ⁻)
    (C⁻ : framing⁺.is-composable⁻ G θ⁺) where

    open tower G θ⁻ θ⁺ S C⁺ C⁻ public
    open unital G θ⁻ θ⁺ S C⁺ C⁻ pin⁻ᴿ pin⁺ᴿ K⁻ᴿ K⁺ᴿ public
```

The negative far flank is idempotent: associativity moves the two
copies together and the derived left unit absorbs one.

```agda
    idem⁻ : ∀ {x y} (n : hom x y) → (n ⨾⁻ θ⁻ y) ⨾⁻ θ⁻ y ≡ n ⨾⁻ θ⁻ y
    idem⁻ {y = y} n =
      assoc⁻ n (θ⁻ y) (θ⁻ y) ∙ ap (n ⨾⁻_) (unitl⁻ (θ⁻ y))
```

## The cuts do not read the witness

Two witnesses whose pairs agree induce the same composites, and the
embedding condition identifies the two representatives. So the cut
edges are the same wherever the pairs are.

```agda
module transport-cuts {o h} (G : virtual-graph o h) (open virtual-graph G)
  (S : reflect-is-embedding G) (R R' : shape.is-framed G)
  (e : (x : ob) → R x .fst ≡ R' x .fst) where

  open shape G

  composite⁺-path : ∀ {x y z} (f : hom x y) (g : hom y z)
    → framing⁻.composite⁺ G (rx-of (frame-of R)) f g
    ≡ framing⁻.composite⁺ G (rx-of (frame-of R')) f g
  composite⁺-path f g i = framing⁻.composite⁺ G (rx-of (λ x → e x i)) f g

  composite⁻-path : ∀ {x y z} (f : hom x y) (g : hom y z)
    → framing⁺.composite⁻ G (corx-of (frame-of R)) f g
    ≡ framing⁺.composite⁻ G (corx-of (frame-of R')) f g
  composite⁻-path f g i = framing⁺.composite⁻ G (corx-of (λ x → e x i)) f g

  agree⁺ : (C : framing⁻.is-composable⁺ G (rx-of (frame-of R)))
           (C' : framing⁻.is-composable⁺ G (rx-of (frame-of R')))
         → ∀ {x y z} (f : hom x y) (g : hom y z) → C f g .fst ≡ C' f g .fst
  agree⁺ C C' f g = ap fst
    (S (framing⁻.composite⁺ G (rx-of (frame-of R')) f g)
       (C f g .fst , C f g .snd ∙ composite⁺-path f g)
       (C' f g))

  agree⁻ : (C : framing⁺.is-composable⁻ G (corx-of (frame-of R)))
           (C' : framing⁺.is-composable⁻ G (corx-of (frame-of R')))
         → ∀ {x y z} (f : hom x y) (g : hom y z) → C f g .fst ≡ C' f g .fst
  agree⁻ C C' f g = ap fst
    (S (framing⁺.composite⁻ G (corx-of (frame-of R')) f g)
       (C f g .fst , C f g .snd ∙ composite⁻-path f g)
       (C' f g))
```
