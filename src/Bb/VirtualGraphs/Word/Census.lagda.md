A census of candidate pairs at the word model, against the two
conditions that a candidate can carry on its own: the equivalence tier
with the self-referential clauses, and candidate invertibility with
candidate readback.

The tier returns the half-twist pair here, with no clause read. The negative
cut against an edge is the positive cut against its shift. So the
negative hand of the tier makes the shift a two-sided unit of the
positive cut. A two-sided unit of that cut is the identity descriptor,
by the bound an injective weakly monotone denotation gives. The shift
is the identity descriptor at the unit translation alone.

The two clauses alone do not return the half-twist pair. `ω̂` reads zero at
zero and translates by two above it, and `(ω̂ , ε̂)` satisfies both
clauses. The first clause is the weaker half. It holds at every pair
whose second component is the identity descriptor. Four degenerate
pairs fail, two on each clause.

Candidate invertibility reduces to one-sided inversion. Its negative
half asks the shift of the first component for a right inverse landing
at the identity descriptor. Its positive half asks the second component
for a left inverse landing at the unit translation. The half-twist pair
carries both. `(ω̂ , ε̂)` fails the negative half with no inhabitant,
since the shift of `ω̂` misses the value one. Four further pairs fail by
carrying two inverses, and one by carrying none.

Candidate readback pins the frame to the half-twist pair, with no tier read.
The recognition equation makes the two translations mutually inverse by
associativity alone. The candidates carrying it contract, and the tier,
both clauses, and invertibility transport back along the pinning.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Word.Census where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥; ¬_; ex-falso)
open import Core.Data.Nat
open import Core.Data.List
open import Core.Equiv
open import Core.Function.Embedding using (equiv→lc)
open import Core.HLevel.Base
  using (Π-is-prop; Πi-is-prop; is-prop-×; Σ-prop-path; Π-is-hlevel; ×-is-hlevel)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Mediation
open import Bb.VirtualGraphs.Recognition
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Word.Carrier
open import Bb.VirtualGraphs.Word.Model
open import Bb.VirtualGraphs.Word.Mediation
  using (half-twist-pair-is-eqv) renaming (half-twists to clause-half-twists)

open Nat using (_+_; _-_; _<_; _≤_; s<s; suc; step)

open self BW (λ _ → τ̂) (λ _ → ε̂) BW-embedding BW-comp⁺ BW-comp⁻
  using ( _⨾⁺_; _⨾⁻_; pair; corr₀; corr₁
        ; is-eqv⁺; is-eqv⁻; is-eqv-pair; is-eqv-pair-is-prop
        ; selfclause₀; selfclause₁; selfmediates₂; framed; framed-is-prop )

open candidate BW
  using (frame; var; covar; coact-π; act-π; rb)
open candidate-absorbing BW
  using (inv⁻; inv⁺; inv)
```

## Separating two descriptors

Two descriptors separate where their denotations separate at one
argument, and monus reads that separation as a positive number.

```agda
monus-self : ∀ n → (n - n) ≡ Z
monus-self Z     = refl
monus-self (S n) = monus-self n

nat-sep : ∀ {m n} → pos? (n - m) → ¬ (m ≡ n)
nat-sep {n = n} q e = subst pos? (ap (n -_) e ∙ monus-self n) q

word-sep : ∀ {A B : W} (n : Nat) → pos? (evW A n - evW B n) → ¬ (A ≡ B)
word-sep n q e = nat-sep q (sym (ap (λ X → evW X n) e))
```

## The unit of the positive cut

A two-sided unit of the positive cut is the identity descriptor. Its
denotation is injective, so it climbs at least as fast as the argument.
Its inverse climbs too, and the two bounds meet.

```agda
mono : (A : W) {j k : Nat} → j ≤ k → evW A j ≤ evW A k
mono A {j} {k} = ev-mono-le (A .fst) (A .snd .fst) (w-inc A) j k

strict : ∀ {m n} → m ≤ n → ¬ (m ≡ n) → m < n
strict suc      ne = ex-falso (ne refl)
strict (step q) ne = q

succ-sep : ∀ {n} → ¬ (n ≡ S n)
succ-sep {n} e = Nat.lt.irrefl (subst (n <_) (sym e) suc)

ev-cancel : (A B : W) → (∀ n → evW A (evW B n) ≡ n)
          → ∀ {m n} → evW B m ≡ evW B n → m ≡ n
ev-cancel A B h {m} {n} e = sym (h m) ∙ ap (evW A) e ∙ h n

ev-ge : (B : W) → (∀ {m n} → evW B m ≡ evW B n → m ≡ n)
      → ∀ n → n ≤ evW B n
ev-ge B lc Z     = Nat.lt.z<s
ev-ge B lc (S n) = Nat.le.cat (s<s (ev-ge B lc n)) (s<s rise)
  where
  rise : evW B n < evW B (S n)
  rise = strict (ev-mono-suc (B .fst) (B .snd .fst) (w-inc B) n)
                (λ e → succ-sep (lc e))

ptw : (A B : W) → A ⨾⁺ B ≡ ε̂ → ∀ n → evW A (evW B n) ≡ n
ptw A B q n = sym (ev-comp A B n) ∙ ap (λ X → evW X n) q ∙ Nat.add.unitr n

unit-is-ε : (e g : W) → e ⨾⁺ g ≡ ε̂ → g ⨾⁺ e ≡ ε̂ → e ≡ ε̂
unit-is-ε e g r l = ev-inj e ε̂ λ n →
  Nat.≤-antisym (at-most n) (at-least n) ∙ sym (Nat.add.unitr n)
  where
  he : ∀ n → evW e (evW g n) ≡ n
  he = ptw e g r

  hg : ∀ n → evW g (evW e n) ≡ n
  hg = ptw g e l

  at-least : ∀ n → n ≤ evW e n
  at-least = ev-ge e (ev-cancel g e hg)

  at-most : ∀ n → evW e n ≤ n
  at-most n = subst (evW e n ≤_) (he n) (mono e (ev-ge g (ev-cancel e g he) n))
```

One hand of the tier suffices. Write `t` for the translation that puts
the edge first. The inverse image of the identity descriptor under `t`
is a right inverse of the edge. `t` is injective, so the same
descriptor is a left inverse.

```agda
post-unit : (e : W) → is-equiv (λ h → e ⨾⁺ h) → e ≡ ε̂
post-unit e E = unit-is-ε e g right left
  where
  cut : W ≃ W
  cut = (λ h → e ⨾⁺ h) , E

  g : W
  g = Equiv.inv cut ε̂

  right : e ⨾⁺ g ≡ ε̂
  right = Equiv.counit cut ε̂

  left : g ⨾⁺ e ≡ ε̂
  left = equiv→lc E
    ( sym (comp-assoc e g e)
    ∙ ap (_⨾⁺ e) right
    ∙ comp-unitl e
    ∙ sym (comp-unitr e) )

φ-unit : (a : W) → φW a ≡ ε̂ → a ≡ τ̂
φ-unit a q = ev-inj a τ̂ λ n →
  sym (ev-φ a (S n)) ∙ ap (λ X → evW X (S n)) q ∙ sym (Nat.add.+suc n Z)
```

## The tier returns the half-twist pair

The negative cut against an edge is the positive cut against the shift
of that edge. So the negative hand of the tier makes the shift a
two-sided unit. The shift is the identity descriptor at the unit
translation and nowhere else.

```agda
pin-pos : (b : W) → is-eqv⁺ {tt} b → b ≡ ε̂
pin-pos b E = post-unit b (E .snd tt)

pin-neg : (a : W) → is-eqv⁻ {tt} a → a ≡ τ̂
pin-neg a E = φ-unit a (post-unit (φW a) (E .snd tt))

tier-pins : (p : pair tt) → is-eqv-pair tt p → p ≡ (τ̂ , ε̂)
tier-pins p E i = pin-neg (p .fst) (E .fst) i , pin-pos (p .snd) (E .snd) i
```

## The clauses alone

At the half-twist pair the self-referential clauses are the clauses read at
the half-twists, term for term.

```agda
half-twists : selfmediates₂ tt (τ̂ , ε̂)
half-twists = clause-half-twists
```

The first clause reads the second component at both flanks and in the
correction. At the identity descriptor those three readings cancel, and
the clause holds whatever the first component is.

```agda
slack₀ : (a : W) → selfclause₀ tt (a , ε̂)
slack₀ a = ap (λ X → ε̂ ⨾⁺ (X ⨾⁻ ε̂)) (sym (comp-unitl a))
```

`ω̂` reads zero at zero and translates by two above it. It satisfies
both clauses against the identity descriptor, and it is not the unit
translation. So the two clauses do not return the half-twist pair. The tier
excludes it.

```agda
ω̂ : W
ω̂ = Z ∷ [] , S (S Z) , tt

ω-mediates : selfmediates₂ tt (ω̂ , ε̂)
ω-mediates = slack₀ ω̂ , refl

ω-not-half-twist : ¬ (_≡_ {A = pair tt} (ω̂ , ε̂) (τ̂ , ε̂))
ω-not-half-twist e = subst w-nil (sym (ap fst e)) tt

ω-not-eqv : ¬ is-eqv-pair tt (ω̂ , ε̂)
ω-not-eqv E = subst w-nil (sym (pin-neg ω̂ (E .fst))) tt

clauses-alone : Σ p ∶ pair tt , (selfmediates₂ tt p × ¬ (p ≡ (τ̂ , ε̂)))
clauses-alone = (ω̂ , ε̂) , (ω-mediates , ω-not-half-twist)
```

The four degenerate pairs all fail. Where the second component is the
identity descriptor the first clause holds and the second fails. Where
it is the unit translation the first clause already fails.

```agda
εε-yes₀ : selfclause₀ tt (ε̂ , ε̂)
εε-yes₀ = slack₀ ε̂

εε-no₁ : ¬ selfclause₁ tt (ε̂ , ε̂)
εε-no₁ = word-sep (S (S Z)) tt

δε-yes₀ : selfclause₀ tt (δ̂ , ε̂)
δε-yes₀ = slack₀ δ̂

δε-no₁ : ¬ selfclause₁ tt (δ̂ , ε̂)
δε-no₁ = word-sep (S (S (S (S Z)))) tt

ττ-no₀ : ¬ selfclause₀ tt (τ̂ , τ̂)
ττ-no₀ e = word-sep Z tt (sym e)

ετ-no₀ : ¬ selfclause₀ tt (ε̂ , τ̂)
ετ-no₀ e = word-sep Z tt (sym e)

εε-no : ¬ selfmediates₂ tt (ε̂ , ε̂)
εε-no M = εε-no₁ (M .snd)

δε-no : ¬ selfmediates₂ tt (δ̂ , ε̂)
δε-no M = δε-no₁ (M .snd)

ττ-no : ¬ selfmediates₂ tt (τ̂ , τ̂)
ττ-no M = ττ-no₀ (M .fst)

ετ-no : ¬ selfmediates₂ tt (ε̂ , τ̂)
ετ-no M = ετ-no₀ (M .fst)
```

## The contraction

The tier returns the pair, and the words form a set. So the framed
pairs contract at the one object, and the family over the objects is a
proposition.

```agda
selfmediates₂-is-prop : (p : pair tt) → is-prop (selfmediates₂ tt p)
selfmediates₂-is-prop p = is-prop-× (W-set _ _) (W-set _ _)

framed-is-prop-at : (p : pair tt)
                  → is-prop (is-eqv-pair tt p × selfmediates₂ tt p)
framed-is-prop-at p =
  is-prop-× (is-eqv-pair-is-prop tt p) (selfmediates₂-is-prop p)

recognize₂ : (p : pair tt)
           → is-eqv-pair tt p × selfmediates₂ tt p → p ≡ (τ̂ , ε̂)
recognize₂ p E = tier-pins p (E .fst)

centre : is-eqv-pair tt (τ̂ , ε̂) × selfmediates₂ tt (τ̂ , ε̂)
centre = half-twist-pair-is-eqv , half-twists

WW-set : is-set (W × W)
WW-set = ×-is-hlevel (S (S Z)) W-set W-set

recognition₂ : (p : pair tt)
             → (is-eqv-pair tt p × selfmediates₂ tt p) ≃ (p ≡ (τ̂ , ε̂))
recognition₂ p =
  iso→equiv (recognize₂ p)
            (λ e → subst (λ q → is-eqv-pair tt q × selfmediates₂ tt q)
                         (sym e) centre)
            (λ E → framed-is-prop-at p _ E)
            (λ e → WW-set p (τ̂ , ε̂) _ e)

framed-contr : (x : ⊤) → is-contr (framed x)
framed-contr _ .center = (τ̂ , ε̂) , centre
framed-contr _ .paths (p , E) =
  sym (Σ-prop-path framed-is-prop-at (recognize₂ p E))

has-framing-is-prop : is-prop ((x : ⊤) → framed x)
has-framing-is-prop = framed-is-prop framed-contr
```

## Candidate invertibility reduces to one-sided inversion

Both action maps land in a function type valued in the descriptors,
which form a set, so each fiber condition is a condition on a
descriptor alone.

```agda
frame-at : W → W → frame
frame-at a b = (λ _ → a) , (λ _ → b)
```

The coterm-side map composes the shift of the first component with the
edge and then with the argument. Evaluation of the fiber equation at
the identity descriptor collapses the argument. The unit law then
returns the collapsed form.

```agda
coact-iso : (a b e : W)
          → (coact-π (frame-at a b) {tt} {tt} e ≡ snd) ≃ (comp (φW a) e ≡ ε̂)
coact-iso a b e =
  iso→equiv to fro (λ w → Π⁻-set _ _ _ w) (λ q → W-set _ _ _ q)
  where
  to : coact-π (frame-at a b) {tt} {tt} e ≡ snd → comp (φW a) e ≡ ε̂
  to pe = sym (comp-unitr (comp (φW a) e)) ∙ happly pe (tt , ε̂)

  fro : comp (φW a) e ≡ ε̂ → coact-π (frame-at a b) {tt} {tt} e ≡ snd
  fro q = funext λ γ → ap (λ X → comp X (γ .snd)) q ∙ comp-unitl (γ .snd)
```

The term-side map runs the other way. The varying quantifier sits in
the shifted slot, and the second component sits outside it. Evaluation
at the unit translation collapses the shifted slot, since the shift of
that translation is the identity descriptor.

```agda
far : (c : W) → comp (φW c) τ̂ ≡ c
far c = sym (comp-unitr (comp (φW c) τ̂)) ∙ act-τ c

act-iso : (a b e : W)
        → (act-π (frame-at a b) {tt} {tt} e ≡ snd) ≃ (comp e b ≡ τ̂)
act-iso a b e =
  iso→equiv to fro (λ w → Π⁺-set _ _ _ w) (λ q → W-set _ _ _ q)
  where
  to : act-π (frame-at a b) {tt} {tt} e ≡ snd → comp e b ≡ τ̂
  to pe = sym (ap (λ X → comp X b) (comp-unitl e)) ∙ happly pe (tt , τ̂)

  fro : comp e b ≡ τ̂ → act-π (frame-at a b) {tt} {tt} e ≡ snd
  fro q = funext λ t →
      comp-assoc (φW (t .snd)) e b
    ∙ ap (comp (φW (t .snd))) q
    ∙ far (t .snd)

fiber⁻≃ : (a b : W)
        → fiber (coact-π (frame-at a b) {tt} {tt}) snd
        ≃ (Σ e ∶ W , comp (φW a) e ≡ ε̂)
fiber⁻≃ a b = Σ-equiv-snd λ e → coact-iso a b e

fiber⁺≃ : (a b : W)
        → fiber (act-π (frame-at a b) {tt} {tt}) snd ≃ (Σ e ∶ W , comp e b ≡ τ̂)
fiber⁺≃ a b = Σ-equiv-snd λ e → act-iso a b e

inv⁻-in : (a b : W) → is-contr (Σ e ∶ W , comp (φW a) e ≡ ε̂) → inv⁻ (frame-at a b) tt
inv⁻-in a b c = is-contr-equiv (fiber⁻≃ a b) c

inv⁻-out : (a b : W) → inv⁻ (frame-at a b) tt → is-contr (Σ e ∶ W , comp (φW a) e ≡ ε̂)
inv⁻-out a b c = is-contr-equiv (esym (fiber⁻≃ a b)) c

inv⁺-in : (a b : W) → is-contr (Σ e ∶ W , comp e b ≡ τ̂) → inv⁺ (frame-at a b) tt
inv⁺-in a b c = is-contr-equiv (fiber⁺≃ a b) c

inv⁺-out : (a b : W) → inv⁺ (frame-at a b) tt → is-contr (Σ e ∶ W , comp e b ≡ τ̂)
inv⁺-out a b c = is-contr-equiv (esym (fiber⁺≃ a b)) c
```

## The half-twist pair

The shift of the unit translation is the identity descriptor. So the
negative half is the left unit law, and its fiber contracts at that
descriptor. The second half-twist is that descriptor. So the positive half
is the right unit law, and its fiber contracts at the unit
translation.

```agda
τε-inv⁻ : is-contr (Σ e ∶ W , comp (φW τ̂) e ≡ ε̂)
τε-inv⁻ .center = ε̂ , comp-unitl ε̂
τε-inv⁻ .paths (e , q) =
  sym (Σ-prop-path (λ _ → W-set _ _) (sym (comp-unitl e) ∙ q))

τε-inv⁺ : is-contr (Σ e ∶ W , comp e ε̂ ≡ τ̂)
τε-inv⁺ .center = τ̂ , comp-unitr τ̂
τε-inv⁺ .paths (e , q) =
  sym (Σ-prop-path (λ _ → W-set _ _) (sym (comp-unitr e) ∙ q))

half-twists-inv : inv (frame-at τ̂ ε̂) tt
half-twists-inv = inv⁻-in τ̂ ε̂ τε-inv⁻ , inv⁺-in τ̂ ε̂ τε-inv⁺
```

## Small arithmetic

Three translations of a literal past the argument, and one predicate
separating the value one from zero and from two upward.

```agda
suc1 : (k : Nat) → k + S Z ≡ S k
suc1 k = Nat.add.+suc k Z ∙ ap S (Nat.add.unitr k)

suc2 : (k : Nat) → k + S (S Z) ≡ S (S k)
suc2 k = Nat.add.+suc k (S Z) ∙ ap S (suc1 k)

suc3 : (k : Nat) → k + S (S (S Z)) ≡ S (S (S k))
suc3 k = Nat.add.+suc k (S (S Z)) ∙ ap S (suc2 k)

one? : Nat → Type
one? Z         = ⊥
one? (S Z)     = ⊤
one? (S (S _)) = ⊥
```

## The pairs without an inverse, and the pairs with two

The shift of `ω̂` prepends a zero. So it reads zero at zero and at one,
and it reads the argument from two upward. The value one is outside its
image, so the negative half has no inhabitant.

```agda
ω-miss : (m : Nat) → ¬ (evW (φW ω̂) m ≡ S Z)
ω-miss Z         e = subst one? (sym e) tt
ω-miss (S Z)     e = subst one? (sym e) tt
ω-miss (S (S k)) e = subst one? (sym (sym (suc2 k) ∙ e)) tt

ωε-empty : ¬ (Σ e ∶ W , comp (φW ω̂) e ≡ ε̂)
ωε-empty (e , q) = ω-miss (evW e (S Z)) (ptw (φW ω̂) e q (S Z))

ωε-no-inv⁻ : ¬ inv⁻ (frame-at ω̂ ε̂) tt
ωε-no-inv⁻ c = ωε-empty (inv⁻-out ω̂ ε̂ c .center)
```

Where the first component is the identity descriptor, its shift is the
double half-twist. That descriptor drops one value, so both the unit
translation and `ω̂` invert it on the right. The negative half then has
two inhabitants.

```agda
δτ : comp δ̂ τ̂ ≡ ε̂
δτ = refl

δω : comp δ̂ ω̂ ≡ ε̂
δω = ev-inj (comp δ̂ ω̂) ε̂ λ n → ev-comp δ̂ ω̂ n ∙ val n
  where
  val : (n : Nat) → evW δ̂ (evW ω̂ n) ≡ evW ε̂ n
  val Z     = refl
  val (S k) = ap (evW δ̂) (suc2 k)

εx-no-inv⁻ : (b : W) → ¬ inv⁻ (frame-at ε̂ b) tt
εx-no-inv⁻ b c =
  subst w-nil
    (ap fst (is-contr→is-prop (inv⁻-out ε̂ b c) (τ̂ , δτ) (ω̂ , δω))) tt
```

Where the second component is the unit translation, the positive half
has two inhabitants as well. One is the identity descriptor. The other
reads one at zero and the argument above it.

```agda
κ̂ : W
κ̂ = S Z ∷ [] , S Z , tt

ετ-cut : comp ε̂ τ̂ ≡ τ̂
ετ-cut = comp-unitl τ̂

κτ-cut : comp κ̂ τ̂ ≡ τ̂
κτ-cut = ev-inj (comp κ̂ τ̂) τ̂ λ n → ev-comp κ̂ τ̂ n ∙ ap (evW κ̂) (suc1 n)

xτ-no-inv⁺ : (a : W) → ¬ inv⁺ (frame-at a τ̂) tt
xτ-no-inv⁺ a c =
  subst w-nil
    (ap fst (is-contr→is-prop (inv⁺-out a τ̂ c) (ε̂ , ετ-cut) (κ̂ , κτ-cut))) tt
```

Where the first component is the double half-twist, its shift drops two
values. The pure translation by two inverts it on the right. So does
the descriptor that reads zero at zero and translates by three above
it.

```agda
ν̂ : W
ν̂ = [] , S (S Z) , tt

μ̂ : W
μ̂ = Z ∷ [] , S (S (S Z)) , tt

φδν : comp (φW δ̂) ν̂ ≡ ε̂
φδν = ev-inj (comp (φW δ̂) ν̂) ε̂ λ n →
  ev-comp (φW δ̂) ν̂ n ∙ ap (evW (φW δ̂)) (suc2 n)

φδμ : comp (φW δ̂) μ̂ ≡ ε̂
φδμ = ev-inj (comp (φW δ̂) μ̂) ε̂ λ n → ev-comp (φW δ̂) μ̂ n ∙ val n
  where
  val : (n : Nat) → evW (φW δ̂) (evW μ̂ n) ≡ evW ε̂ n
  val Z     = refl
  val (S k) = ap (evW (φW δ̂)) (suc3 k)

δx-no-inv⁻ : (b : W) → ¬ inv⁻ (frame-at δ̂ b) tt
δx-no-inv⁻ b c =
  subst w-nil
    (ap fst (is-contr→is-prop (inv⁻-out δ̂ b c) (ν̂ , φδν) (μ̂ , φδμ))) tt
```

Where the second component is the double half-twist, the positive half is
empty. That descriptor reads zero at zero and at one, so a left inverse
would read one and two at the same argument.

```agda
xδ-empty : (e : W) → ¬ (comp e δ̂ ≡ τ̂)
xδ-empty e q = subst one? (sym (k Z) ∙ k (S Z)) tt
  where
  k : (n : Nat) → evW e (evW δ̂ n) ≡ evW τ̂ n
  k n = sym (ev-comp e δ̂ n) ∙ ap (λ X → evW X n) q

xδ-no-inv⁺ : (a : W) → ¬ inv⁺ (frame-at a δ̂) tt
xδ-no-inv⁺ a c = xδ-empty (w .fst) (w .snd)
  where
  w : Σ e ∶ W , comp e δ̂ ≡ τ̂
  w = inv⁺-out a δ̂ c .center
```

## The census

```agda
ωε-no-inv : ¬ inv (frame-at ω̂ ε̂) tt
ωε-no-inv I = ωε-no-inv⁻ (I .fst)

εε-no-inv : ¬ inv (frame-at ε̂ ε̂) tt
εε-no-inv I = εx-no-inv⁻ ε̂ (I .fst)

ετ-no-inv : ¬ inv (frame-at ε̂ τ̂) tt
ετ-no-inv I = εx-no-inv⁻ τ̂ (I .fst)

ττ-no-inv : ¬ inv (frame-at τ̂ τ̂) tt
ττ-no-inv I = xτ-no-inv⁺ τ̂ (I .snd)

δε-no-inv : ¬ inv (frame-at δ̂ ε̂) tt
δε-no-inv I = δx-no-inv⁻ ε̂ (I .fst)

τδ-no-inv : ¬ inv (frame-at τ̂ δ̂) tt
τδ-no-inv I = xδ-no-inv⁺ τ̂ (I .snd)
```

## Candidate readback

The recognition equation at a candidate says that the composite of two
translations is the identity in both orders. So each translation is the
inverse of the other, and the leading one is an equivalence. The
identity descriptor comes back from that hand, and the unit translation
comes back from its shift. The second component follows by the unit
law.

```agda
rb-is-prop : (p : frame) → is-prop (rb p)
rb-is-prop p = Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → W-set _ _

half-twist-frame : frame
half-twist-frame = frame-at τ̂ ε̂

rb-half-twists : rb half-twist-frame
rb-half-twists f = sandwich f

module recognize (p : frame) (R : rb p) where
  a b : W
  a = p .fst tt
  b = p .snd tt

  cut back : W → W
  cut h = comp (φW a) h
  back h = comp h b

  sec : (h : W) → back (cut h) ≡ h
  sec h = R {tt} {tt} h

  retr : (h : W) → cut (back h) ≡ h
  retr h = sym (comp-assoc (φW a) h b) ∙ R {tt} {tt} h

  cut-equiv : is-equiv cut
  cut-equiv = iso→equiv cut back sec retr .snd

  φ-is-ε : φW a ≡ ε̂
  φ-is-ε = post-unit (φW a) cut-equiv

  pin-a : a ≡ τ̂
  pin-a = φ-unit a φ-is-ε

  pin-b : b ≡ ε̂
  pin-b = sym (comp-unitl b)
        ∙ ap (λ X → comp X b) (sym φ-is-ε)
        ∙ ap (λ X → comp X b) (sym (comp-unitr (φW a)))
        ∙ R {tt} {tt} ε̂

rb-pins : (p : frame) → rb p → p ≡ half-twist-frame
rb-pins p R i = (λ _ → recognize.pin-a p R i) , (λ _ → recognize.pin-b p R i)

rb-contr : is-contr (Σ q ∶ frame , rb q)
rb-contr .center = half-twist-frame , rb-half-twists
rb-contr .paths (p , R) = sym (Σ-prop-path rb-is-prop (rb-pins p R))
```

The pinning returns the framing itself, so everything the other
conditions assert at the half-twist pair transports back along it.

```agda
rb→inv : (p : frame) → rb p → inv p tt
rb→inv p R = subst (λ q → inv q tt) (sym (rb-pins p R)) half-twists-inv

pair-path : (p : frame) → rb p
          → _≡_ {A = W × W} (p .fst tt , p .snd tt) (τ̂ , ε̂)
pair-path p R i = recognize.pin-a p R i , recognize.pin-b p R i

rb→eqv : (p : frame) → rb p → is-eqv-pair tt (p .fst tt , p .snd tt)
rb→eqv p R =
  subst (is-eqv-pair tt) (sym (pair-path p R)) half-twist-pair-is-eqv

rb→clauses : (p : frame) → rb p → selfmediates₂ tt (p .fst tt , p .snd tt)
rb→clauses p R = subst (selfmediates₂ tt) (sym (pair-path p R)) half-twists
```
