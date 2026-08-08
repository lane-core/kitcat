Recognition over the circle model, in its three forms: the
candidate-relative kit, the per-object shape, and the cross-pair
grammar.

Each action map at a candidate is a two-sided multiplication with one
flank held at a component of the candidate, so the invertibility
condition holds at every pair. The recognition equation instead
selects: it holds exactly where the two components cancel, which is
one whole circle of candidates, and the type of candidates carrying
it retracts onto that circle. So neither condition alone contracts,
and neither does their conjunction. At the axiom pair the recognition
equation is the right unit law of the multiplication, and its
`rot`-shift is a second witness one winding away.

The per-object shape reads the same data at one object. Every
cancelling pair carries the half-twist predicate, the recognition type
retracts onto the circle, and the sandwich clause is not a
proposition.

The cross-pair grammar reads the sandwich over the connecting homs,
and the recognized pairs form the same circle. Its gluing clause is
empty at every pair, the axiom pair included: a clause at any pair
reads every adjacent sandwich, and the circle supplies one for every
value, which would make the unhalf-twist cancel against every point at
once.

This module uses `--cubical`: it consumes `loop-nontrivial` and
`Circle-is-groupoid` in unerased positions, which ride the winding
equivalence `ua` builds. The circle modules form their own import
island; no `--erased-cubical` module imports them unerased.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Recognition where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty using (¬_; ⊥)
open import Core.Data.Nat.Type using (Z)
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Transport.J using (J; subst)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-prop→is-set)
open import Core.HLevel.Base using (Π-is-prop; retract→is-hlevel)
open import Core.Equiv.Base
  using (_≃_; Equiv; is-contr-equiv; iso→equiv; eqv-fibers)
open import Core.Equiv.Properties using (Σ-equiv-snd)

open import HData.Circle
open Circle using (base; loop; rot; ind; mult; mult-unit-r; mult-assoc;
                   mult-equiv; mult-r-equiv; mult-faithful; loop-nontrivial;
                   Circle-is-groupoid)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Recognition
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Degenerate.Shape
open import Bb.VirtualGraphs.Degenerate.Gluing
open import Bb.VirtualGraphs.Circle.Model
```

## The candidate kit

Each action map is a two-sided multiplication with one flank held at
a component of the candidate. The recognition equation multiplies the
edge between the two components and asks for the edge back. Left
multiplication by the axiom is the identity on the nose, so no
further factor appears.

```agda
module frames where

  open candidate circle.model public
  open candidate-absorbing circle.model public

  mk : Circle → Circle → frame
  mk a b = (λ _ → a) , (λ _ → b)

  coact-value : (a b e r : Circle)
              → coact-π (mk a b) {tt} {tt} e (tt , r) ≡ mult a (mult e r)
  coact-value _ _ _ _ = refl

  act-value : (a b e l : Circle)
            → act-π (mk a b) {tt} {tt} e (tt , l) ≡ mult l (mult e b)
  act-value _ _ _ _ = refl

  rb-out : (a b : Circle) → rb (mk a b) → (f : Circle) → mult a (mult f b) ≡ f
  rb-out a b R f = R {tt} {tt} f

  rb-in : (a b : Circle) → ((f : Circle) → mult a (mult f b) ≡ f) → rb (mk a b)
  rb-in a b w f = w f
```

The coterm side reassociates onto one left multiplication, and the
first slot of the multiplication is faithful, so its fiber is the
fiber of left translation by the negative component. The term side
keeps the varying quantifier outside; evaluation at the axiom frees
it, and the fiber becomes the fiber of right translation by the
positive component. Both translations are equivalences at every
point, so invertibility holds at every candidate.

```agda
  slice⁻ : (a b e : Circle)
         → (coact-π (mk a b) {tt} {tt} e ≡ snd)
         ≃ ((r : Circle) → mult a (mult e r) ≡ r)
  slice⁻ a b e = iso→equiv
    (λ w r i → w i (tt , r))
    (λ v i γ → v (γ .snd) i)
    (λ _ → refl) (λ _ → refl)

  reassoc : (a e : Circle)
          → ((r : Circle) → mult a (mult e r) ≡ r)
          ≃ ((r : Circle) → mult (mult a e) r ≡ r)
  reassoc a e = iso→equiv
    (λ w r → mult-assoc a e r ∙ w r)
    (λ v r → sym (mult-assoc a e r) ∙ v r)
    (λ w → funext λ r → Path.lc (mult-assoc a e r) (w r))
    (λ v → funext λ r → Path.lc (sym (mult-assoc a e r)) (v r))

  inv⁻-all : (p : frame) → inv⁻ p tt
  inv⁻-all p =
    is-contr-equiv (Σ-equiv-snd λ e → slice⁻ (p .fst tt) (p .snd tt) e)
      (is-contr-equiv (Σ-equiv-snd λ e → reassoc (p .fst tt) e)
        (is-contr-equiv (Σ-equiv-snd λ e → mult-faithful (mult (p .fst tt) e) base)
          (mult-equiv (p .fst tt) .eqv-fibers base)))

  eval-free : (c : Circle) → ((l : Circle) → mult l c ≡ l) ≃ (c ≡ base)
  eval-free c = iso→equiv to fro sec retr
    where
    to : ((l : Circle) → mult l c ≡ l) → c ≡ base
    to w = w base

    fro : c ≡ base → (l : Circle) → mult l c ≡ l
    fro v l = ap (mult l) v ∙ mult-unit-r l

    sec : (w : (l : Circle) → mult l c ≡ l) → fro (to w) ≡ w
    sec w = funext (ind (λ l → fro (to w) l ≡ w l)
      (Path.unitr (w base))
      (is-prop→PathP (λ i → Circle-is-groupoid _ _ _ _)
        (Path.unitr (w base)) (Path.unitr (w base))))

    retr : (v : c ≡ base) → to (fro v) ≡ v
    retr v = Path.unitr v

  slice⁺ : (a b e : Circle)
         → (act-π (mk a b) {tt} {tt} e ≡ snd)
         ≃ ((l : Circle) → mult l (mult e b) ≡ l)
  slice⁺ a b e = iso→equiv
    (λ w l i → w i (tt , l))
    (λ v i t → v (t .snd) i)
    (λ _ → refl) (λ _ → refl)

  inv⁺-all : (p : frame) → inv⁺ p tt
  inv⁺-all p =
    is-contr-equiv (Σ-equiv-snd λ e → slice⁺ (p .fst tt) (p .snd tt) e)
      (is-contr-equiv (Σ-equiv-snd λ e → eval-free (mult e (p .snd tt)))
        (mult-r-equiv (p .snd tt) .eqv-fibers base))

  inv-all : (p : frame) → inv p tt
  inv-all p = inv⁻-all p , inv⁺-all p
```

The recognition equation at a candidate is a section of the family
that multiplies the edge between the two components. At the axiom it
says the two components cancel, and that one equation is also
sufficient: the rotation family is `mult`-equivariant in the second
slot and commutes past every path, so the section extends over the
loop.

```agda
  rb-base : (a b : Circle) → rb (mk a b) → mult a b ≡ base
  rb-base a b R = rb-out a b R base

  mult-ap-rot : (a b : Circle) → ap (mult a) (rot b) ≡ rot (mult a b)
  mult-ap-rot = ind (λ a → (b : Circle) → ap (mult a) (rot b) ≡ rot (mult a b))
    (λ b → refl)
    (is-prop→PathP (λ i → Π-is-prop λ b → Circle-is-groupoid _ _ _ _) _ _)

  rot-square : {x y : Circle} (q : x ≡ y) → PathP (λ i → rot x i ≡ rot y i) q q
  rot-square {x} q =
    J (λ y' q' → PathP (λ i → rot x i ≡ rot y' i) q' q') (λ i j → rot x i) q

  extend : (a b : Circle) → mult a b ≡ base → (f : Circle) → mult a (mult f b) ≡ f
  extend a b q = ind (λ f → mult a (mult f b) ≡ f) q
    (subst (λ L → PathP (λ i → L i ≡ loop i) q q) (sym (mult-ap-rot a b))
           (rot-square q))

  rb-cancel : (a b : Circle) → mult a b ≡ base → rb (mk a b)
  rb-cancel a b q = rb-in a b (extend a b q)
```

The recognition equation therefore holds at every pair whose two
components cancel and at no other pair. That is one whole circle of
candidates, onto which the total space retracts. Invertibility holds
at every pair here, so the retraction survives it.

```agda
  binv : Circle → Circle
  binv a = Equiv.inv (mult a , mult-equiv a) base

  bcounit : (a : Circle) → mult a (binv a) ≡ base
  bcounit a = Equiv.counit (mult a , mult-equiv a) base

  sect-rb : Circle → Σ q ∶ frame , rb q
  sect-rb a = mk a (binv a) , rb-cancel a (binv a) (bcounit a)

  head-rb : (Σ q ∶ frame , rb q) → Circle
  head-rb z = z .fst .fst tt

  rb-not-contr : is-contr (Σ q ∶ frame , rb q) → ⊥
  rb-not-contr c = loop-nontrivial (is-prop→is-set pr base base loop refl)
    where
    pr : is-prop Circle
    pr = is-contr→is-prop (retract→is-hlevel Z head-rb sect-rb (λ _ → refl) c)

  sect-both : Circle → Σ q ∶ frame , (inv q tt × rb q)
  sect-both a =
    mk a (binv a) , (inv-all (mk a (binv a)) , rb-cancel a (binv a) (bcounit a))

  head-both : (Σ q ∶ frame , (inv q tt × rb q)) → Circle
  head-both z = z .fst .fst tt

  both-not-contr : is-contr (Σ q ∶ frame , (inv q tt × rb q)) → ⊥
  both-not-contr c = loop-nontrivial (is-prop→is-set pr base base loop refl)
    where
    pr : is-prop Circle
    pr = is-contr→is-prop (retract→is-hlevel Z head-both sect-both (λ _ → refl) c)
```

The two conditions separate here. Invertibility holds at every pair.
The recognition equation cannot, since it would identify every point
of the circle with the axiom. At the axiom pair the equation is the
right unit law, and its `rot`-shift is a second witness one winding
away.

```agda
  rb-not-all : ((q : frame) → rb q) → ⊥
  rb-not-all R = loop-nontrivial (is-prop→is-set pr base base loop refl)
    where
    to-base : (x : Circle) → x ≡ base
    to-base x = R (mk base x) {tt} {tt} base

    pr : is-prop Circle
    pr x y = to-base x ∙ sym (to-base y)

  inv-not→rb : ((q : frame) → inv q tt → rb q) → ⊥
  inv-not→rb H = rb-not-all λ q → H q (inv-all q)

  r₀ r₁ : rb (mk base base)
  r₀ f = mult-unit-r f
  r₁ f = mult-unit-r f ∙ rot f

  rb-not-prop : is-prop (rb (mk base base)) → ⊥
  rb-not-prop W =
    loop-nontrivial (sym (Path.unitl loop) ∙ sym (λ i → W r₀ r₁ i {tt} {tt} base))
```

## The per-object shape

The shape reads the same data at one object. The axiom pair carries
it, and so does every cancelling pair, so the recognized pairs form
one circle: the Σ does not contract, the framing type is not a
proposition, and no map identifies the pairs of any two witnesses.

```agda
module shapes where

  open shape circle.model public

  flanksᶜ : flanks (base , base)
  flanksᶜ f = frames.r₀ f

  half-twistᶜ : is-half-twist (base , base)
  half-twistᶜ = flanksᶜ , frames.inv-all (frames.mk base base)

  framedᶜ : is-framed
  framedᶜ _ = (base , base) , half-twistᶜ

  cutsᶜ : cuts framedᶜ
  cutsᶜ = (λ f g → circle.cc⁺ f g) , (λ f g → circle.cc⁻ f g)

  deductiveᶜ : is-deductive-system-depreciated
  deductiveᶜ = circle.stable , framedᶜ , cutsᶜ

  sect : Circle → Σ p ∶ pair tt , is-half-twist p
  sect a = (a , frames.binv a)
         , (λ f → frames.sect-rb a .snd f)
         , frames.inv-all (frames.mk a (frames.binv a))

  head : (Σ p ∶ pair tt , is-half-twist p) → Circle
  head z = z .fst .fst

  Σ-prop-refuted : is-prop (Σ p ∶ pair tt , is-half-twist p) → ⊥
  Σ-prop-refuted pr = loop-nontrivial (is-prop→is-set prC base base loop refl)
    where
      prC : is-prop Circle
      prC x y = ap head (pr (sect x) (sect y))

  not-contrᶜ : is-contr (Σ p ∶ pair tt , is-half-twist p) → ⊥
  not-contrᶜ c = Σ-prop-refuted (is-contr→is-prop c)

  framed-not-propᶜ : is-prop is-framed → ⊥
  framed-not-propᶜ W =
    Σ-prop-refuted (λ u v i → W (λ _ → u) (λ _ → v) i tt)

  uniq-refutedᶜ : ((p q : Σ p' ∶ pair tt , is-half-twist p') → p .fst ≡ q .fst) → ⊥
  uniq-refutedᶜ U = loop-nontrivial (is-prop→is-set pr base base loop refl)
    where
      to-base : (a : Circle) → a ≡ base
      to-base a = ap fst (U (sect a) (sect base))

      pr : is-prop Circle
      pr x y = to-base x ∙ sym (to-base y)
```

The sandwich clause is not a proposition at the axiom pair: its two
witnesses separate by one winding.

```agda
  flanks-not-propᶜ : is-prop (flanks (base , base)) → ⊥
  flanks-not-propᶜ W =
    loop-nontrivial (sym (Path.unitl loop) ∙ sym (λ i → W f₀ f₁ i base))
    where
      f₀ f₁ : flanks (base , base)
      f₀ f = frames.r₀ f
      f₁ f = frames.r₁ f
```

## The cross-pair grammar

The sandwich at a cross pair converts to the recognition equation, so
a pair carries it exactly when its components cancel. The recognized
pairs form one circle, and the total space retracts onto it.

```agda
module crossings where

  open grammar circle.model public

  sand-in : (u v : Circle) → mult u v ≡ base → sand tt tt (u , v)
  sand-in u v q f = frames.extend u v q f

  sand-out : (u v : Circle) → sand tt tt (u , v) → mult u v ≡ base
  sand-out u v R = R base

  sectᵇ : Circle → Σ c ∶ cross tt tt , is-cross tt tt c
  sectᵇ a = (a , frames.binv a)
    , sand-in a (frames.binv a) (frames.bcounit a)
    , frames.inv-all (frames.mk a (frames.binv a))

  headᵇ : (Σ c ∶ cross tt tt , is-cross tt tt c) → Circle
  headᵇ z = z .fst .fst

  freedomᵇ : is-contr (Σ c ∶ cross tt tt , is-cross tt tt c) → ⊥
  freedomᵇ c = loop-nontrivial (is-prop→is-set pr base base loop refl)
    where
      pr : is-prop Circle
      pr = is-contr→is-prop (retract→is-hlevel Z headᵇ sectᵇ (λ _ → refl) c)
```

A gluing clause at any pair reads every adjacent sandwich. Right
translation is an equivalence, so every value of the circle is the
second component of a cancelling pair, and the clause makes the first
component cancel against every value at once. That makes the circle a
proposition, so the predicate on a cross pair is empty at every pair,
the axiom pair included.

```agda
  kill : (u v : Circle) → glue⁻ tt tt (u , v) → (c : Circle) → mult u c ≡ base
  kill u v GL c =
    sand-out u c (GL (w .fst , c) (sand-in (w .fst) c (w .snd)))
    where
      w : fiber (λ z → mult z c) base
      w = mult-r-equiv c .eqv-fibers base .center

  prop-circle : (u : Circle) → ((c : Circle) → mult u c ≡ base) → is-prop Circle
  prop-circle u H c₁ c₂ =
    sym (E.unit c₁) ∙ ap E.inv (H c₁ ∙ sym (H c₂)) ∙ E.unit c₂
    where
      module E = Equiv (mult u , mult-equiv u)

  no-predᶜ : (u v : Circle) → ¬ pred tt tt (u , v)
  no-predᶜ u v P = loop-nontrivial
    (is-prop→is-set (prop-circle u (kill u v (P .snd .fst)))
      base base loop refl)

  no-pred-baseᶜ : ¬ pred tt tt (base , base)
  no-pred-baseᶜ = no-predᶜ base base

  emptyᶜ : ¬ (Σ c ∶ cross tt tt , pred tt tt c)
  emptyᶜ z = no-predᶜ (z .fst .fst) (z .fst .snd) (z .snd)

  not-contrᶜ : is-contr (Σ c ∶ cross tt tt , pred tt tt c) → ⊥
  not-contrᶜ c = emptyᶜ (c .center)
```
