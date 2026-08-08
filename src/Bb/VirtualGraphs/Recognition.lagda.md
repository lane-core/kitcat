Framings as candidates. A candidate framing is two families of
endo-edges, and every condition below quantifies over one instead of
reading a field of the carrier. Two action maps anchor at the
candidate: `inv⁻` and `inv⁺` ask each of them for a contractible
fiber over the second projection, and `rb` asks reflection at the
candidate's own axiom to return the edge. The judgment-level
composites `_⊛⁺_` and `_⊛⁻_` cut judgments through the candidate, and
two words in them are the clauses `clause₀` and `clause₁`. At a
framing that carries both cuts, those clauses are exactly two
edge-level equations.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Recognition where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.HLevel.Base using (is-prop-×)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Mediation
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

## The clauses at a framing

A framing supplies one candidate among the others. There each
judgment-level composite is that hand's cut read through `reflect`,
by the representation law of the cut and nothing else.

```agda
module at-framing {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower G rx corx S C⁺ C⁻ public

  tf : candidate.frame G
  tf = rx , corx

  open clause G tf public

  w⁺ : ∀ {x y z} (f : hom x y) (g : hom y z) → (⟦ f ⟧ ⊛⁺ ⟦ g ⟧) ≡ ⟦ f ⨾⁺ g ⟧
  w⁺ f g = sym (reflect-⨾⁺ f g)

  w⁻ : ∀ {x y z} (f : hom x y) (g : hom y z) → (⟦ f ⟧ ⊛⁻ ⟦ g ⟧) ≡ ⟦ f ⨾⁻ g ⟧
  w⁻ f g = sym (reflect-⨾⁻ f g)
```

The two clauses read at this candidate are the two edge-level
equations `Mediation` states over an arbitrary candidate pair, read
at the pair the framing itself supplies.

```agda
  private module M = mediation G rx corx S C⁺ C⁻

  pair : (x : ob) → M.pair x
  pair x = rx x , corx x

  lead₁ : (x : ob) → hom x x
  lead₁ x = M.corr₁ (pair x)

  law₀ law₁ : (x : ob) → Type h
  law₀ x = M.clause₀ x (pair x)
  law₁ x = M.clause₁ x (pair x)
```

Each side of each clause collapses onto the reflection of its edge
word. The collapse walks the word from the inside out, one
representation law per junction.

```agda
  left₀ : (x : ob)
        → (pos x ⊛⁺ (neg x ⊛⁻ pos x))
        ≡ ⟦ corx x ⨾⁺ (rx x ⨾⁻ corx x) ⟧
  left₀ x = ap (pos x ⊛⁺_) (w⁻ (rx x) (corx x))
          ∙ w⁺ (corx x) (rx x ⨾⁻ corx x)

  right₀ : (x : ob)
         → (corr₀ x ⊛⁺ ((pos x ⊛⁺ neg x) ⊛⁻ pos x))
         ≡ ⟦ corx x ⨾⁺ ((corx x ⨾⁺ rx x) ⨾⁻ corx x) ⟧
  right₀ x =
      ap (pos x ⊛⁺_)
         ( ap (_⊛⁻ pos x) (w⁺ (corx x) (rx x))
         ∙ w⁻ (corx x ⨾⁺ rx x) (corx x) )
    ∙ w⁺ (corx x) ((corx x ⨾⁺ rx x) ⨾⁻ corx x)

  left₁ : (x : ob)
        → (neg x ⊛⁺ (pos x ⊛⁻ pos x))
        ≡ ⟦ rx x ⨾⁺ (corx x ⨾⁻ corx x) ⟧
  left₁ x = ap (neg x ⊛⁺_) (w⁻ (corx x) (corx x))
          ∙ w⁺ (rx x) (corx x ⨾⁻ corx x)

  mid₁ : (x : ob) → corr₁ x ≡ ⟦ lead₁ x ⟧
  mid₁ x =
      ap (neg x ⊛⁺_)
         ( ap (pos x ⊛⁺_) (w⁻ (corx x) (corx x))
         ∙ w⁺ (corx x) (corx x ⨾⁻ corx x) )
    ∙ w⁺ (rx x) (corx x ⨾⁺ (corx x ⨾⁻ corx x))

  tail₁ : (x : ob)
        → ((neg x ⊛⁺ pos x) ⊛⁻ pos x)
        ≡ ⟦ (rx x ⨾⁺ corx x) ⨾⁻ corx x ⟧
  tail₁ x = ap (_⊛⁻ pos x) (w⁺ (rx x) (corx x))
          ∙ w⁻ (rx x ⨾⁺ corx x) (corx x)

  right₁ : (x : ob)
         → (corr₁ x ⊛⁺ ((neg x ⊛⁺ pos x) ⊛⁻ pos x))
         ≡ ⟦ lead₁ x ⨾⁺ ((rx x ⨾⁺ corx x) ⨾⁻ corx x) ⟧
  right₁ x = (λ i → mid₁ x i ⊛⁺ tail₁ x i)
           ∙ w⁺ (lead₁ x) ((rx x ⨾⁺ corx x) ⨾⁻ corx x)
```

The embedding condition cancels `reflect`, so at this candidate the
clause and its edge-level equation carry each other.

```agda
  to₀ : (x : ob) → law₀ x → clause₀ x
  to₀ x e = left₀ x ∙ ap reflect e ∙ sym (right₀ x)

  to₁ : (x : ob) → law₁ x → clause₁ x
  to₁ x e = left₁ x ∙ ap reflect e ∙ sym (right₁ x)

  from₀ : (x : ob) → clause₀ x → law₀ x
  from₀ x e = lc (sym (left₀ x) ∙ e ∙ right₀ x)

  from₁ : (x : ob) → clause₁ x → law₁ x
  from₁ x e = lc (sym (left₁ x) ∙ e ∙ right₁ x)
```
