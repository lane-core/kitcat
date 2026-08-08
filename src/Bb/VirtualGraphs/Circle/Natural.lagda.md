Naturality over two circle carriers.

At the circle model both half-twists sit at the axiom and absorb, so each
hand gains its near unit law outright. The naturality equation holds
in both hands as well — definitionally in the positive one — so the
model carries a point in each centred pair and all four unit laws.
What it refutes is the contractibility each tier asks for: the homs
are the circle, and a tier would make them a set. Read at the axiom,
the readback predicate and the negative far unit law are one type,
and the readback modulus, the negative naturality modulus, and the
positive naturality modulus are each free by one winding, with the
map from the first to the second carrying the generator to the
inverse generator.

The path groupoid over the circle, framed by the rotation family on
the negative side and by reflexivity on the positive side, carries
both tiers instead. There all four unit laws fail, both crossed cuts
fail, the negative half-twist is not idempotent, and every triple
associates.

This module uses `--cubical`: it consumes `loop-nontrivial` and
`Circle-is-groupoid` in unerased positions, which ride the winding
equivalence `ua` builds. The circle modules form their own import
island; no `--erased-cubical` module imports them unerased.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Natural where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty using (¬_; ⊥)
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base using (ap-comp)
open import Core.Groupoid using (sym-distr)

open import HData.Circle
open Circle using (base; loop; rot; mult; mult-unit-r; mult-assoc;
                   ap-mult-base; slide-rot; loop-nontrivial;
                   Circle-is-groupoid)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Naturality
open import Bb.VirtualGraphs.Degenerate.Tower
open import Bb.VirtualGraphs.Groupoid.Path using (module naturality)
open import Bb.VirtualGraphs.Circle.Model
open import Bb.VirtualGraphs.Circle.Torsor using (rb₀; rb₁)
```

## The circle model absorbs

Reflection at either half-twist is a translation by the axiom, so both
cancellations hold and the half-twists absorb. Three of the four
hypotheses are the right unit law of the multiplication, and the
fourth is definitional.

```agda
module absorbing where

  open virtual-graph circle.model public using (ob; hom; judgment; reflect)
  open transfer circle.model (λ _ → base) (λ _ → base)
    circle.stable circle.C⁺ circle.C⁻ public
  open framing circle.model (λ _ → base) (λ _ → base) public
    using (axiom; eval; readback-of; cell⁻; cell⁺; own⁻; own⁺;
           is-natural⁻; is-natural⁺; is-naturalᴶ⁻; is-naturalᴶ⁺)

  pin⁻ : ∀ x → coact-π {x} {x} base ≡ cell⁻ x
  pin⁻ _ = funext λ γ → sym (mult-unit-r (γ .snd))

  pin⁺ : ∀ x → act-π {x} {x} base ≡ cell⁺ x
  pin⁺ _ = funext λ t → mult-unit-r (t .snd)

  K⁻ : ∀ x → cell⁻ x ≡ snd
  K⁻ _ = funext λ γ → mult-unit-r (γ .snd)

  K⁺ : ∀ x → cell⁺ x ≡ snd
  K⁺ _ = refl

  open unital circle.model (λ _ → base) (λ _ → base)
    circle.stable circle.C⁺ circle.C⁻ pin⁻ pin⁺ K⁻ K⁺ public
```

## The naturality equation holds in both hands

The positive hand is definitional: each side evaluates the argument
and multiplies the edge between the two flanks. The negative hand
crosses the right unit law twice and associativity once. Each
equation then supplies its hand's square and a point of its hand's
centred pair.

```agda
  naturalᴶ⁻ : is-naturalᴶ⁻
  naturalᴶ⁻ m = funext λ γ →
      ap (λ t → mult t (mult m (γ .snd .snd))) (mult-unit-r (γ .fst .snd))
    ∙ sym (mult-assoc (γ .fst .snd) m (γ .snd .snd))
    ∙ sym (ap (λ t → mult (mult (γ .fst .snd) t) (γ .snd .snd)) (mult-unit-r m))

  naturalᴶ⁺ : is-naturalᴶ⁺
  naturalᴶ⁺ _ = refl

  square⁻ : nat⁻-law
  square⁻ = fromᴶ⁻ naturalᴶ⁻

  square⁺ : nat⁺-law
  square⁺ = fromᴶ⁺ naturalᴶ⁺

  centre⁻ : ∀ {x y} (m : hom x y) → own⁻ m
  centre⁻ = centreᴶ⁻ naturalᴶ⁻

  centre⁺ : ∀ {x y} (m : hom x y) → own⁺ m
  centre⁺ = centreᴶ⁺ naturalᴶ⁺
```

Absorption supplies one unit law per hand and the equation supplies
the other, so all four hold. The homs are the circle, which is not a
set, and each tier makes the homs a set, so each tier is refuted.

```agda
  far⁻ : unitr⁻-law
  far⁻ = natural.unitr⁻ naturalᴶ⁻

  far⁺ : unitl⁺-law
  far⁺ = natural.unitl⁺ naturalᴶ⁺

  no-natural⁻ : ¬ is-natural⁻
  no-natural⁻ N = loop-nontrivial (sym (natural.hom-set⁻ N base base refl loop))

  no-natural⁺ : ¬ is-natural⁺
  no-natural⁺ N = loop-nontrivial (sym (natural.hom-set⁺ N base base refl loop))
```

## The negative naturality modulus

A pointwise shift by the rotation carries a witness of the negative
equation to another witness. The two separate at the axiom by one
winding, so the equation is not a proposition, and no family over it
with points over both witnesses has a contractible total space.

```agda
  shiftᴶ⁻ : is-naturalᴶ⁻ → is-naturalᴶ⁻
  shiftᴶ⁻ q m = q m ∙ λ i γ → rot (composite⁻ m base γ) i

  nj₀ nj₁ : is-naturalᴶ⁻
  nj₀ = naturalᴶ⁻
  nj₁ = shiftᴶ⁻ naturalᴶ⁻

  separate⁻ : nj₀ {tt} {tt} base ≡ nj₁ {tt} {tt} base → ⊥
  separate⁻ P = loop-nontrivial (sym λ i j → sep i j (axiom tt))
    where
      u : composite⁻ base base ≡ composite⁻ base base
      u = nj₀ base

      Λ : composite⁻ base base ≡ composite⁻ base base
      Λ i γ = rot (composite⁻ base base γ) i

      sep : refl ≡ Λ
      sep = sym (Path.invl u) ∙ ap (sym u ∙_) P ∙ Path.lc u Λ

  naturalᴶ⁻-not-prop : is-prop is-naturalᴶ⁻ → ⊥
  naturalᴶ⁻-not-prop W = separate⁻ (λ i → W nj₀ nj₁ i base)

  torsorᴶ⁻ : ∀ {u} (F : is-naturalᴶ⁻ → Type u) → F nj₀ → F nj₁
           → is-contr (Sigma is-naturalᴶ⁻ F) → ⊥
  torsorᴶ⁻ F a b c =
    separate⁻ (λ i → is-contr→is-prop c (nj₀ , a) (nj₁ , b) i .fst base)
```

## The positive naturality modulus

The positive hand carries the same shift, applied pointwise at its
own target judgment.

```agda
  shiftᴶ⁺ : is-naturalᴶ⁺ → is-naturalᴶ⁺
  shiftᴶ⁺ q m = q m ∙ λ i γ → rot (composite⁺ m base γ) i

  nk₀ nk₁ : is-naturalᴶ⁺
  nk₀ = naturalᴶ⁺
  nk₁ = shiftᴶ⁺ naturalᴶ⁺

  separate⁺ : nk₀ {tt} {tt} base ≡ nk₁ {tt} {tt} base → ⊥
  separate⁺ P =
    loop-nontrivial (sym λ i j → Path.wind (nk₀ {tt} {tt} base) Λ P i j (axiom tt))
    where
      Λ : composite⁺ base base ≡ composite⁺ base base
      Λ i γ = rot (composite⁺ base base γ) i

  naturalᴶ⁺-not-prop : is-prop is-naturalᴶ⁺ → ⊥
  naturalᴶ⁺-not-prop W = separate⁺ (λ i → W nk₀ nk₁ i base)

  torsorᴶ⁺ : ∀ {u} (F : is-naturalᴶ⁺ → Type u) → F nk₀ → F nk₁
           → is-contr (Sigma is-naturalᴶ⁺ F) → ⊥
  torsorᴶ⁺ F a b c =
    separate⁺ (λ i → is-contr→is-prop c (nk₀ , a) (nk₁ , b) i .fst base)
```

## The readback modulus against the negative one

The negative cut of the model is the multiplication and the negative
half-twist is the axiom, so reflection at the axiom multiplies the edge by
the axiom on the right: the readback predicate and the far unit law
of the negative hand are one type here. Absorption supplies the near
unit law of the negative hand with no naturality hypothesis, so the
readback maps to the negative naturality equation, and the far law
maps back. The negative half-twist is idempotent outright.

```agda
  readback-is-far⁻ : readback-of ≡ unitr⁻-law
  readback-is-far⁻ = refl

  shiftᴿ : readback-of → readback-of
  shiftᴿ R f = R f ∙ rot f

  ν⁻ : readback-of → nat⁻-law
  ν⁻ R m = unitl⁻ m ∙ sym (R m)

  to⁻ : readback-of → is-naturalᴶ⁻
  to⁻ R = judg⁻ (ν⁻ R)

  from⁻ : is-naturalᴶ⁻ → readback-of
  from⁻ = natural.unitr⁻

  free-idem⁻ : idem⁻-law
  free-idem⁻ _ = unitl⁻ base
```

Each modulus has a witness at the axiom edge, and such a witness is a
loop at the axiom once the argument is the axiom. Reading there gives
one measure into the loop space, and each shift adds one `loop` to
it.

```agda
  wᴿ : readback-of → base ≡ base
  wᴿ R = R {tt} {tt} base

  wᴿ-shift : (R : readback-of) → wᴿ (shiftᴿ R) ≡ wᴿ R ∙ loop
  wᴿ-shift _ = refl

  wᴶ⁻ : is-naturalᴶ⁻ → base ≡ base
  wᴶ⁻ q = ap (eval {tt} {tt}) (q {tt} {tt} base)

  wᴶ⁻-shift : (q : is-naturalᴶ⁻) → wᴶ⁻ (shiftᴶ⁻ q) ≡ wᴶ⁻ q ∙ loop
  wᴶ⁻-shift q = ap-comp (eval {tt} {tt}) (q {tt} {tt} base) Λ
    where
      Λ : composite⁻ base base ≡ composite⁻ base base
      Λ i γ = rot (composite⁻ base base γ) i

  wᴶ⁺ : is-naturalᴶ⁺ → base ≡ base
  wᴶ⁺ q = ap (eval {tt} {tt}) (q {tt} {tt} base)

  wᴶ⁺-shift : (q : is-naturalᴶ⁺) → wᴶ⁺ (shiftᴶ⁺ q) ≡ wᴶ⁺ q ∙ loop
  wᴶ⁺-shift q = ap-comp (eval {tt} {tt}) (q {tt} {tt} base) Λ
    where
      Λ : composite⁺ base base ≡ composite⁺ base base
      Λ i γ = rot (composite⁺ base base γ) i
```

The negative cut's witness at the axiom pair is trivial once the
argument is the axiom: each of its three steps is `refl` there. The
measure of the image then inverts the measure of the argument, with
the near law at the axiom edge translating it. One step of the
readback shift becomes one step of the inverse naturality shift, so
one shift on each side cancels.

```agda
  cut-at : base ≡ base
  cut-at = ap (eval {tt} {tt}) (reflect-⨾⁻ {x = tt} {y = tt} {z = tt} base base)

  cut-trivial : cut-at ≡ refl
  cut-trivial = ap sym (Path.unitl (refl ∙ refl) ∙ Path.unitl refl)

  wᴶ⁻-to : (R : readback-of) → wᴶ⁻ (to⁻ R) ≡ unitl⁻ base ∙ sym (wᴿ R)
  wᴶ⁻-to R =
      ap-comp (eval {tt} {tt}) (sym cut) (ap reflect n ∙ cut)
    ∙ ap (sym cut-at ∙_) (ap-comp (eval {tt} {tt}) (ap reflect n) cut)
    ∙ ap (λ z → sym cut-at ∙ (z ∙ cut-at)) (ap-mult-base n)
    ∙ ap (λ z → sym z ∙ (n ∙ z)) cut-trivial
    ∙ Path.unitl (n ∙ refl)
    ∙ Path.unitr n
    where
      cut : reflect (base ⨾⁻ base) ≡ composite⁻ base base
      cut = reflect-⨾⁻ {x = tt} {y = tt} {z = tt} base base

      n : base ≡ base
      n = ν⁻ R {tt} {tt} base

  to⁻-shift : (R : readback-of) → wᴶ⁻ (to⁻ (shiftᴿ R)) ≡ wᴶ⁻ (to⁻ R) ∙ sym loop
  to⁻-shift R =
      wᴶ⁻-to (shiftᴿ R)
    ∙ ap (unitl⁻ base ∙_) (sym-distr (wᴿ R) loop)
    ∙ ap (unitl⁻ base ∙_) (slide-rot (sym (wᴿ R)))
    ∙ Path.assoc (unitl⁻ base) (sym (wᴿ R)) (sym loop)
    ∙ ap (_∙ sym loop) (sym (wᴶ⁻-to R))

  generators : (R : readback-of)
             → wᴶ⁻ (shiftᴶ⁻ (to⁻ (shiftᴿ R))) ≡ wᴶ⁻ (to⁻ R)
  generators R =
      wᴶ⁻-shift (to⁻ (shiftᴿ R))
    ∙ ap (_∙ loop) (to⁻-shift R)
    ∙ Path.rc (sym loop) (wᴶ⁻ (to⁻ R))

  generators-at-readback : wᴶ⁻ (shiftᴶ⁻ (to⁻ rb₁)) ≡ wᴶ⁻ (to⁻ rb₀)
  generators-at-readback = generators rb₀
```

## The path groupoid at the rotation family

Take the path groupoid over the circle, with the rotation family on
the negative side and reflexivity on the positive side. Both tiers
hold, since the circle is a groupoid. Every law below reduces to a
value of the loop space at the axiom, so `loop-nontrivial` refutes
it.

```agda
module turn where

  open naturality rot public
  open tiers Circle-is-groupoid public

  ι : hom base base
  ι = refl

  round : ι ⨾⁺ ι ≡ loop
  round = cut⁺-value ι ι ∙ Path.unitl (loop ∙ refl) ∙ Path.unitr loop

  no-unitl⁻ : ¬ unitl⁻-law
  no-unitl⁻ U =
    loop-nontrivial (sym (Path.unitr loop) ∙ sym (cut⁻-value loop ι) ∙ U ι)

  no-unitr⁻ : ¬ unitr⁻-law
  no-unitr⁻ U =
    loop-nontrivial (sym (Path.unitl loop) ∙ sym (cut⁻-value ι loop) ∙ U ι)

  no-unitl⁺ : ¬ unitl⁺-law
  no-unitl⁺ U = loop-nontrivial (sym round ∙ U ι)

  no-unitr⁺ : ¬ unitr⁺-law
  no-unitr⁺ U = loop-nontrivial (sym round ∙ U ι)
```

The negative half-twist is not idempotent in its own hand, and neither
crossed cut holds. Each reduces to a double loop against a single
one.

```agda
  halve : loop ∙ loop ≡ loop → loop ≡ refl
  halve e = sym (Path.lc loop loop) ∙ ap (sym loop ∙_) e ∙ Path.invl loop

  no-idem⁻ : ¬ idem⁻-law
  no-idem⁻ I = loop-nontrivial (halve (sym (cut⁻-value loop loop) ∙ I base))

  cut⁻-cross-law cut⁺-cross-law : Type
  cut⁻-cross-law = ∀ {x y z} (f : hom x y) (g : hom y z) → cross⁻ f ⨾⁺ g ≡ f ⨾⁻ g
  cut⁺-cross-law = ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ cross⁺ g ≡ f ⨾⁺ g

  no-cut⁻-cross : ¬ cut⁻-cross-law
  no-cut⁻-cross X = loop-nontrivial (sym lhs ∙ X ι ι ∙ rhs)
    where
      flank : cross⁻ ι ≡ ι
      flank = cut⁻-value {base} {base} {base} ι refl ∙ Path.unitl refl

      lhs : cross⁻ ι ⨾⁺ ι ≡ loop
      lhs = ap (_⨾⁺ ι) flank ∙ round

      rhs : ι ⨾⁻ ι ≡ refl
      rhs = cut⁻-value ι ι ∙ Path.unitl refl

  no-cut⁺-cross : ¬ cut⁺-cross-law
  no-cut⁺-cross X = loop-nontrivial (halve (sym lhs ∙ X ι ι ∙ round))
    where
      flank : cross⁺ ι ≡ loop ∙ loop
      flank = cut⁺-value loop ι ∙ ap (loop ∙_) (Path.unitr loop)

      lhs : ι ⨾⁻ cross⁺ ι ≡ loop ∙ loop
      lhs = cut⁻-value ι (cross⁺ ι) ∙ Path.unitl (cross⁺ ι) ∙ flank
```

Both cuts are path composition with one fixed insertion, so every
triple associates.

```agda
  all-associate : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
                → associates f g h
  all-associate {x = x} f g h =
      cut⁻-value (f ⨾⁺ g) h
    ∙ ap (_∙ h) (cut⁺-value f g)
    ∙ sym (Path.assoc f (rot x ∙ g) h)
    ∙ ap (f ∙_) (sym (Path.assoc (rot x) g h))
    ∙ sym (ap (λ w' → f ∙ (rot x ∙ w')) (cut⁻-value g h))
    ∙ sym (cut⁺-value f (g ⨾⁻ h))
```
