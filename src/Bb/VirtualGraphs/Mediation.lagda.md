Mediation over a candidate pair, and the framing read among the
candidates. `Tower` withholds the mixed word whose junctions run
positive then negative, so its two bracketings need not agree. A
candidate pair mediates at such a word when a word in the pair, cut in
front of one bracketing, gives the other. Two triples of half-twists
carry the statement. The self-referential form reads the same two
corrections at the triples the pair builds out of itself, so its
clauses name no half-twist family.

Read at the pair the framing itself supplies, those clauses are the
judgment-level clauses `Recognition` states, collapsed onto the
reflection of an edge word. The embedding condition cancels `reflect`,
so the two readings carry each other.

The telescope is both half-twist families, the embedding condition,
and both cuts.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Mediation where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.HLevel.Base using (Π-is-prop; is-prop-×)
open import Core.Equiv.Properties using (is-equiv-is-prop)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Canonical
open import Bb.VirtualGraphs.Recognition
```

## The two clauses

A candidate at an object is a pair of endo-edges there. The first
component stands where `rx` stands and the second where `corx` does.
`corr₀` and `corr₁` are two words in the pair: the second component
alone, and the first component cut before a word in the second.

Each clause takes one triple of half-twists and corrects the mixed word
there. `clause₀` reads the triple `(corx x , rx x , corx x)` and
corrects with `corr₀`. `clause₁` reads `(rx x , corx x , corx x)` and
corrects with `corr₁`. In both, the right bracketing is the left one
with the correction word cut in front of it. `mediates₂` asks for the
two clauses together, and for no other triple.

The equivalence condition reads each component in one hand: the first
in the negative hand, the second in the positive one.

```agda
module mediation {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower G rx corx S C⁺ C⁻ public
  open invertible⁺ G rx S C⁺ public using (is-eqv⁺; eqv-2-out-of-3; module canonical)
  open invertible⁻ G corx S C⁻ public using (is-eqv⁻)

  pair : ob → Type h
  pair x = hom x x × hom x x

  corr₀ : ∀ {x} → pair x → hom x x
  corr₀ p = p .snd

  corr₁ : ∀ {x} → pair x → hom x x
  corr₁ p = p .fst ⨾⁺ (p .snd ⨾⁺ (p .snd ⨾⁻ p .snd))

  clause₀ : (x : ob) → pair x → Type h
  clause₀ x p =
      corx x ⨾⁺ (rx x ⨾⁻ corx x)
    ≡ corr₀ p ⨾⁺ ((corx x ⨾⁺ rx x) ⨾⁻ corx x)

  clause₁ : (x : ob) → pair x → Type h
  clause₁ x p =
      rx x ⨾⁺ (corx x ⨾⁻ corx x)
    ≡ corr₁ p ⨾⁺ ((rx x ⨾⁺ corx x) ⨾⁻ corx x)

  mediates₂ : (x : ob) → pair x → Type h
  mediates₂ x p = clause₀ x p × clause₁ x p

  is-eqv-pair : (x : ob) → pair x → Type (o ⊔ h)
  is-eqv-pair x p = is-eqv⁻ (p .fst) × is-eqv⁺ (p .snd)

  is-eqv-pair-is-prop : (x : ob) (p : pair x) → is-prop (is-eqv-pair x p)
  is-eqv-pair-is-prop x p =
    is-prop-×
      (is-prop-× (Π-is-prop λ _ → is-equiv-is-prop _)
                 (Π-is-prop λ _ → is-equiv-is-prop _))
      (is-prop-× (Π-is-prop λ _ → is-equiv-is-prop _)
                 (Π-is-prop λ _ → is-equiv-is-prop _))
```

A framing at an object is a candidate there with the equivalence
condition and the two clauses. Where every object carries a
contractible one, the whole family is a proposition.

```agda
  framed : (x : ob) → Type (o ⊔ h)
  framed x = Σ p ∶ pair x , (is-eqv-pair x p × mediates₂ x p)

  framed-is-prop : (∀ x → is-contr (framed x)) → is-prop (∀ x → framed x)
  framed-is-prop c = Π-is-prop λ x → is-contr→is-prop (c x)
```

## The self-referential clauses

The self-referential form puts the candidate in every slot of the two
triples: each `corx` becomes the second component and each `rx` the
first. The correction words read the pair alone already, so they
carry over unchanged. Nothing the clauses state names a half-twist family.
Both half-twist families still enter through the two cut hypotheses.
`is-composable⁺` closes the term half at `var`, and `is-composable⁻`
closes the coterm half at `covar`.

```agda
module self {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open mediation G rx corx S C⁺ C⁻ public
    using ( _⨾⁺_; _⨾⁻_; pair; corr₀; corr₁
          ; is-eqv⁺; is-eqv⁻; is-eqv-pair; is-eqv-pair-is-prop )

  selfclause₀ : (x : ob) → pair x → Type h
  selfclause₀ x p =
      p .snd ⨾⁺ (p .fst ⨾⁻ p .snd)
    ≡ corr₀ p ⨾⁺ ((p .snd ⨾⁺ p .fst) ⨾⁻ p .snd)

  selfclause₁ : (x : ob) → pair x → Type h
  selfclause₁ x p =
      p .fst ⨾⁺ (p .snd ⨾⁻ p .snd)
    ≡ corr₁ p ⨾⁺ ((p .fst ⨾⁺ p .snd) ⨾⁻ p .snd)

  selfmediates₂ : (x : ob) → pair x → Type h
  selfmediates₂ x p = selfclause₀ x p × selfclause₁ x p

  framed : (x : ob) → Type (o ⊔ h)
  framed x = Σ p ∶ pair x , (is-eqv-pair x p × selfmediates₂ x p)

  framed-is-prop : (∀ x → is-contr (framed x)) → is-prop (∀ x → framed x)
  framed-is-prop c = Π-is-prop λ x → is-contr→is-prop (c x)
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
