Framings as candidates, over the bare carrier. A candidate framing is
two families of endo-edges, and every condition here quantifies over
one instead of reading a field. Two action maps anchor at the
candidate, `rb` asks reflection at the candidate's own axiom to return
the edge, and the judgment-level composites `_⊛⁺_` and `_⊛⁻_` cut
judgments through it. Two words in those composites are the clauses.

Nothing here reads a cut, an embedding condition, or a composition.
The telescope is `ob`, `hom`, and `reflect`, together with the
candidate itself. `Mediation` states the same clauses over edges,
where a framing and its two cuts are in scope.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Recognition where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel.Base using (is-prop-×)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Framing using (module framing)
```

## The candidate-relative kit

A candidate is a pair of families of endo-edges. The first fills the
term half of an argument and the second fills the coterm half — the
two positions the framing families fill. Neither the carrier's
framing nor a cut is in scope here, so every statement below stands
over `ob`, `hom`, and `reflect` alone.

```agda
module candidate {o h} (G : virtual-graph o h) where
  open virtual-graph G

  frame : Type (o ⊔ h)
  frame = ((x : ob) → hom x x) × ((x : ob) → hom x x)

  var : (p : frame) (x : ob) → term x
  var p x = x , p .fst x

  covar : (p : frame) (y : ob) → coterm y
  covar p y = y , p .snd y

  coact-π : (p : frame) {x y : ob} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π p {x} f γ = reflect f (var p x , γ)

  act-π : (p : frame) {x y : ob} → hom x y → (t : term x) → hom (t .fst) y
  act-π p {y = y} f t = reflect f (t , covar p y)
```

The second condition is readback at the candidate's own axiom:
reflection there returns the edge, at every edge of the carrier.

```agda
  rb : frame → Type (o ⊔ h)
  rb p = framing.readback-of G (p .fst) (p .snd)
```

## The judgment-level cuts

Each cut closes one half of an argument at the framing and then asks
for a representative. Replace the framing by a candidate and withhold
the representative, and what is left is an operation on judgments.
`coactʲ` closes the term half at the candidate's first component,
`actʲ` closes the coterm half at its second, and the two composites
are the cuts before representation.

```agda
module clause {o h} (G : virtual-graph o h) (p : candidate.frame G) where
  open virtual-graph G
  open candidate G using (var; covar)

  ⟦_⟧ : ∀ {x y} → hom x y → judgment x y
  ⟦ f ⟧ = reflect f

  coactʲ : ∀ {x y} → judgment x y → coterm y → coterm x
  coactʲ {x} β γ = γ .fst , β (var p x , γ)

  actʲ : ∀ {x y} → judgment x y → term x → term y
  actʲ {y = y} α t = t .fst , α (t , covar p y)

  infixl 25 _⊛⁺_
  _⊛⁺_ : ∀ {x y z} → judgment x y → judgment y z → judgment x z
  (α ⊛⁺ β) γ = α (γ .fst , coactʲ β (γ .snd))

  infixl 25 _⊛⁻_
  _⊛⁻_ : ∀ {x y z} → judgment x y → judgment y z → judgment x z
  (α ⊛⁻ β) γ = β (actʲ α (γ .fst) , γ .snd)
```

Each component enters a clause through the reflection of its own
edge. The two clauses are equations between words in the composites,
each side built from a fixed number of copies of each component, and
each equation corrected by a leading word.

```agda
  neg pos : (x : ob) → judgment x x
  neg x = ⟦ p .fst x ⟧
  pos x = ⟦ p .snd x ⟧

  corr₀ corr₁ : (x : ob) → judgment x x
  corr₀ x = pos x
  corr₁ x = neg x ⊛⁺ (pos x ⊛⁺ (pos x ⊛⁻ pos x))

  clause₀ clause₁ : (x : ob) → Type (o ⊔ h)
  clause₀ x = pos x ⊛⁺ (neg x ⊛⁻ pos x)
            ≡ corr₀ x ⊛⁺ ((pos x ⊛⁺ neg x) ⊛⁻ pos x)
  clause₁ x = neg x ⊛⁺ (pos x ⊛⁻ pos x)
            ≡ corr₁ x ⊛⁺ ((neg x ⊛⁺ pos x) ⊛⁻ pos x)

  mediates : (x : ob) → Type (o ⊔ h)
  mediates x = clause₀ x × clause₁ x

  mediates-is-prop : (∀ {x y} (α β : judgment x y) → is-prop (α ≡ β))
                   → (x : ob) → is-prop (mediates x)
  mediates-is-prop jp x =
    is-prop-× (jp (pos x ⊛⁺ (neg x ⊛⁻ pos x))
                  (corr₀ x ⊛⁺ ((pos x ⊛⁺ neg x) ⊛⁻ pos x)))
              (jp (neg x ⊛⁺ (pos x ⊛⁻ pos x))
                  (corr₁ x ⊛⁺ ((neg x ⊛⁺ pos x) ⊛⁻ pos x)))
```

Each clause reads one object and readback reads a pair of objects. So
the closure of the clauses quantifies over the objects, and the
conjunction of the two conditions sits inside one Σ over the
candidates.

```agda
selects : ∀ {o h} (G : virtual-graph o h) → candidate.frame G → Type (o ⊔ h)
selects G p = (x : virtual-graph.ob G) → clause.mediates G p x

pinned : ∀ {o h} (G : virtual-graph o h) → Type (o ⊔ h)
pinned G = Σ q ∶ candidate.frame G , (candidate.rb G q × selects G q)
```
