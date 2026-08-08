Polarity at the word model. Homs form a set there, so both polarities
are propositions at the one object, and both are empty: a positivity
witness yields linearity of the identity descriptor `ε̂`, and a
negativity witness yields thunkability of the unit translation `τ̂`.

The two half-twists generate the carrier under the two cuts. `gen-sem`
writes every canonical descriptor as a cut word in them, recursing on
the descriptor: a pure translation peels one unit translation per step,
a zero head is one guard — the negative cut against the identity — and
a positive head keeps every value positive by weak monotonicity, so its
word is the unit translation cut onto the pointwise predecessor, whose
tail value drops by one. The recursion consumes weak monotonicity
alone, and the minimality constraint rides along inside `W`. So the
two-edge check returns the full quantifier here, and each hypothesis
pair fails on exactly one half-twist: `τ̂` is linear and `ε̂` is not, `ε̂`
is thunkable and `τ̂` is not.

Read through the collapse, each refutation gives the other.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Word.Polarity where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat
open import Core.Data.List
open import Core.Data.Bool

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Polarity
open import Bb.VirtualGraphs.Degenerate.Readback
open import Bb.VirtualGraphs.Degenerate.Cancellation
open import Bb.VirtualGraphs.Word.Carrier
open import Bb.VirtualGraphs.Word.Model
open import Bb.VirtualGraphs.Word.Defect
  using (le-pos; ev-τ; ev-cutε; run→linear; rise→thunkable)

open Nat using (_+_; _≤_; _≤ᵇ_; ≤ᵇ-sound; ≤ᵇ-complete)
open List using (length)
open Bool using (So; so-and; so-fst; so-snd)

open polarity BW (λ _ → τ̂) (λ _ → ε̂) BW-embedding BW-comp⁺ BW-comp⁻
open collapse BW (λ _ → τ̂) (λ _ → ε̂) BW-embedding BW-comp⁺ BW-comp⁻
  BW-readback BW-absorbing⁻ BW-absorbing⁺
  using (linear→thunkable; thunkable→linear)
```

## The h-level and the two emptinesses

```agda
positive-prop : is-prop (positive tt)
positive-prop = positive-is-prop (λ {x} {y} → W-set) tt

negative-prop : is-prop (negative tt)
negative-prop = negative-is-prop (λ {x} {y} → W-set) tt

positive-empty : ¬ positive tt
positive-empty P = linear-refuted (P tt ε̂)

negative-empty : ¬ negative tt
negative-empty N = thunkable-refuted (N tt τ̂)
```

## The half-twists generate the model

Each half-twist carries the closure its index reaches: the unit translation
rises nowhere below its plateau, and the identity descriptor rises to
zero.

```agda
linear-τ̂ : linear τ̂
linear-τ̂ = run→linear τ̂ refl

thunkable-ε̂ : thunkable ε̂
thunkable-ε̂ = rise→thunkable ε̂ refl
```

The pointwise predecessor of a descriptor, and the two order facts the
recursion reads off `incr?`.

```agda
mapPred : List Nat → List Nat
mapPred []      = []
mapPred (x ∷ p) = Nat.pred x ∷ mapPred p

ev-mapPred : ∀ p u n → ev (mapPred p) u n ≡ Nat.pred (ev p (S u) n)
ev-mapPred []      u n     = sym (ap Nat.pred (Nat.add.+suc n u))
ev-mapPred (x ∷ p) u Z     = refl
ev-mapPred (x ∷ p) u (S n) = ev-mapPred p u n

incr-mapPred : ∀ p u → So (incr? p (S u)) → So (incr? (mapPred p) u)
incr-mapPred []      u s = tt
incr-mapPred (x ∷ p) u s =
  so-and (Nat.pred x ≤ᵇ ev (mapPred p) u Z) (incr? (mapPred p) u)
    (≤ᵇ-complete (Nat.pred x) (ev (mapPred p) u Z)
      (subst (Nat.pred x ≤_) (sym (ev-mapPred p u Z))
        (Nat.le.pred-mono
          (≤ᵇ-sound x (ev p (S u) Z)
            (so-fst (x ≤ᵇ ev p (S u) Z) (incr? p (S u)) s)))))
    (incr-mapPred p u (so-snd (x ≤ᵇ ev p (S u) Z) (incr? p (S u)) s))

head-le : ∀ x p t → So (incr? (x ∷ p) t) → x ≤ t
head-le x p t s =
  Nat.le.cat
    (≤ᵇ-sound x (ev p t Z) (so-fst (x ≤ᵇ ev p t Z) (incr? p t) s))
    (subst (ev p t Z ≤_) tail-val
      (ev-mono-le p t (so-snd (x ≤ᵇ ev p t Z) (incr? p t) s)
        Z (length p) Nat.lt.z<s))
  where
  tail-val : ev p t (length p) ≡ t
  tail-val =
    subst (λ m → ev p t m ≡ t) (Nat.add.unitr (length p)) (ev-past p t Z)

spred : ∀ v → (Σ j ∶ Nat , v ≡ S j) → S (Nat.pred v) ≡ v
spred v (j , e) = ap (λ m → S (Nat.pred m)) e ∙ sym e
```

Every canonical descriptor is a cut word in the two half-twists, and every
edge is one after transport along `ev-inj`.

```agda
gen-sem : ∀ p t → So (incr? p t)
        → Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev p t n)
gen-sem [] Z s = ε̂ , gen-corx , λ n → refl
gen-sem [] (S u) s = τ̂ ⨾⁺ A' , gen-⨾⁺ gen-rx dA' , path
  where
  ih : Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev [] u n)
  ih = gen-sem [] u tt

  A' : W
  A' = ih .fst

  dA' : gen A'
  dA' = ih .snd .fst

  path : ∀ n → evW (τ̂ ⨾⁺ A') n ≡ ev [] (S u) n
  path n =
    ev-comp τ̂ A' n
    ∙ ap (evW τ̂) (ih .snd .snd n)
    ∙ ev-τ (n + u)
    ∙ sym (Nat.add.+suc n u)
gen-sem (Z ∷ p) t s = A' ⨾⁻ ε̂ , gen-⨾⁻ dA' gen-corx , path
  where
  ih : Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev p t n)
  ih = gen-sem p t (so-snd (Z ≤ᵇ ev p t Z) (incr? p t) s)

  A' : W
  A' = ih .fst

  dA' : gen A'
  dA' = ih .snd .fst

  path : ∀ n → evW (A' ⨾⁻ ε̂) n ≡ ev (Z ∷ p) t n
  path Z     = ev-cutε A' Z
  path (S m) = ev-cutε A' (S m) ∙ ih .snd .snd m
gen-sem (S y ∷ p) Z s =
  ex-falso (Nat.lt.¬n<z (Nat.lt.peel Z (head-le (S y) p Z s)))
gen-sem (S y ∷ p) (S u) s = τ̂ ⨾⁺ A' , gen-⨾⁺ gen-rx dA' , path
  where
  ih : Σ A ∶ W , gen A × (∀ n → evW A n ≡ ev (y ∷ mapPred p) u n)
  ih = gen-sem (y ∷ mapPred p) u (incr-mapPred (S y ∷ p) u s)

  A' : W
  A' = ih .fst

  dA' : gen A'
  dA' = ih .snd .fst

  pos-at : ∀ n → Σ j ∶ Nat , ev (S y ∷ p) (S u) n ≡ S j
  pos-at Z     = y , refl
  pos-at (S m) =
    le-pos y (ev p (S u) m)
      (Nat.le.cat
        (≤ᵇ-sound (S y) (ev p (S u) Z)
          (so-fst (S y ≤ᵇ ev p (S u) Z) (incr? p (S u)) s))
        (ev-mono-le p (S u)
          (so-snd (S y ≤ᵇ ev p (S u) Z) (incr? p (S u)) s)
          Z m Nat.lt.z<s))

  path : ∀ n → evW (τ̂ ⨾⁺ A') n ≡ ev (S y ∷ p) (S u) n
  path n =
    ev-comp τ̂ A' n
    ∙ ap (evW τ̂) (ih .snd .snd n ∙ ev-mapPred (S y ∷ p) u n)
    ∙ ev-τ (Nat.pred (ev (S y ∷ p) (S u) n))
    ∙ spred (ev (S y ∷ p) (S u) n) (pos-at n)

gen-all : (A : W) → gen A
gen-all A =
  subst (λ B → gen B) (ev-inj (g .fst) A (g .snd .snd)) (g .snd .fst)
  where
  g : Σ B ∶ W , gen B × (∀ n → evW B n ≡ evW A n)
  g = gen-sem (A .fst) (A .snd .fst) (w-inc A)
```

Over the generated carrier both half-twists decide each polarity.

```agda
positive-two-edge : linear ε̂ → linear τ̂ → positive tt
positive-two-edge = positive-generated (λ f → gen-all f) tt

negative-two-edge : thunkable ε̂ → thunkable τ̂ → negative tt
negative-two-edge = negative-generated (λ f → gen-all f) tt
```

## Through the collapse

Each half-twist condition implies the other at the one object, so either
refutation gives the other.

```agda
τ̂-not-thunkable : ¬ thunkable τ̂
τ̂-not-thunkable T = linear-refuted (thunkable→linear tt T)

ε̂-not-linear : ¬ linear ε̂
ε̂-not-linear L = thunkable-refuted (linear→thunkable tt L)
```
