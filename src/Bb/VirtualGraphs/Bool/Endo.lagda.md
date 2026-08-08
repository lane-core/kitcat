One object, and the endofunctions of `Bool` for the one edge type,
with the two half-twists a pair of commuting involutions. The carrier
satisfies the embedding condition, both cuts, and both absorption
tiers; each of the four flanking operations is an involution, hence an
equivalence; and every triple associates. Two instances then separate
the flank equations from readback. With both half-twists `not`, all four
unit laws and the round law hold and readback fails. With the negative
half-twist `not` and the positive one the identity, all four unit laws, the
round law, and readback fail together.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Bool.Endo where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false; module Bool)
open import Core.Data.Empty
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)
open import Core.Equiv.Base using (is-equiv; iso→equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower

is-true : Bool → Type
is-true true  = ⊤
is-true false = ⊥

true≢false : true ≡ false → ⊥
true≢false p = subst is-true p tt
```

## The endofunction family

Reflection reads its edge between the two flanks of the argument, so
each hand cuts through the other hand's half-twist: the positive cut
inserts `a` at its junction, the negative cut inserts `b`. The three
hypotheses make `a` and `b` commuting involutions. They do not ask
that `a` and `b` be inverse to each other, and the two composites
`b ∘ a` and `a ∘ b` are involutions as well.

```agda
module endo (a b : Bool → Bool)
  (a-invol : ∀ z → a (a z) ≡ z)
  (b-invol : ∀ z → b (b z) ≡ z)
  (ab-comm : ∀ z → a (b z) ≡ b (a z)) where

  Endo : Type
  Endo = Bool → Bool

  Endo-set : is-set Endo
  Endo-set = Π-is-hlevel 2 λ _ → Bool.set

  ba-invol : ∀ z → b (a (b (a z))) ≡ z
  ba-invol z = ap b (ab-comm (a z)) ∙ b-invol (a (a z)) ∙ a-invol z

  ab-invol : ∀ z → a (b (a (b z))) ≡ z
  ab-invol z =
    ap a (sym (ab-comm (b z))) ∙ ap (λ w → a (a w)) (b-invol z) ∙ a-invol z

  model : virtual-graph 0ℓ 0ℓ
  model .virtual-graph.ob      = ⊤
  model .virtual-graph.hom _ _ = Endo
  model .virtual-graph.reflect m γ z = γ .snd .snd (m (γ .fst .snd z))

  open virtual-graph model
  open framing model (λ _ → a) (λ _ → b) using (readback-of) public
```

The reflection at the two identity flanks returns the edge, so
reflection is injective, and the edges form a set. The word carrying
its own junction half-twist represents each cut, on the nose.

```agda
  reflect-inj : ∀ {x y : ob} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-inj p = happly p ((tt , idfun Bool) , (tt , idfun Bool))

  S : reflect-is-embedding model
  S = embedding-from-injective model (λ {_} {_} → Endo-set) reflect-inj

  C⁺ : framing⁻.is-composable⁺ model (λ _ → a)
  C⁺ f g = (λ z → g (a (f z))) , refl

  C⁻ : framing⁺.is-composable⁻ model (λ _ → b)
  C⁻ f g = (λ z → g (b (f z))) , refl

  open tower model (λ _ → a) (λ _ → b) S C⁺ C⁻ public
```

Each action map is injective by the same reading at the identity
flank, and its target is a set, so each absorption fiber is a
proposition. The negative fiber holds `a` and the positive one holds
`b`, each by its own involution.

```agda
  action-set : is-set ((γ : coterm tt) → hom tt (γ .fst))
  action-set = Π-is-hlevel 2 λ _ → Endo-set

  coact-inj : {e e' : Endo}
            → coact-π {tt} {tt} e ≡ coact-π {tt} {tt} e' → e ≡ e'
  coact-inj {e} {e'} p = funext λ z →
      sym (ap e (a-invol z))
    ∙ happly (happly p (tt , idfun Bool)) (a z)
    ∙ ap e' (a-invol z)

  act-inj : {e e' : Endo}
          → act-π {tt} {tt} e ≡ act-π {tt} {tt} e' → e ≡ e'
  act-inj {e} {e'} p = funext λ z →
      sym (b-invol (e z))
    ∙ ap b (happly (happly p (tt , idfun Bool)) z)
    ∙ b-invol (e' z)

  tier⁻ : absorbing⁻.is-absorbing⁻ model (λ _ → a)
  tier⁻ _ = prop-inhabited→is-contr
    (injective→is-embedding action-set (coact-π {tt} {tt}) coact-inj snd)
    (a , funext λ γ → funext λ z → ap (γ .snd) (a-invol z))

  tier⁺ : absorbing⁺.is-absorbing⁺ model (λ _ → b)
  tier⁺ _ = prop-inhabited→is-contr
    (injective→is-embedding action-set (act-π {tt} {tt}) act-inj snd)
    (b , funext λ t → funext λ z → b-invol (t .snd z))
```

Each flanking operation composes the edge with `b ∘ a` or with
`a ∘ b`, on one side. Both composites are involutions, so each
operation is its own inverse and all four are equivalences. The two
far flanks are the hypotheses `Bb.VirtualGraphs.Degenerate.Neutral`'s `neutral`
module takes.

```agda
  P-invol : ∀ {x y : ob} (m : hom x y) → flanks.P (flanks.P m) ≡ m
  P-invol m = funext λ z → ap m (ba-invol z)

  Q-invol : ∀ {x y : ob} (n : hom x y) → flanks.Q (flanks.Q n) ≡ n
  Q-invol n = funext λ z → ba-invol (n z)

  P'-invol : ∀ {x y : ob} (n : hom x y) → flanks.P' (flanks.P' n) ≡ n
  P'-invol n = funext λ z → ab-invol (n z)

  Q'-invol : ∀ {x y : ob} (m : hom x y) → flanks.Q' (flanks.Q' m) ≡ m
  Q'-invol m = funext λ z → ap m (ab-invol z)

  P-is-equiv : ∀ {x y : ob} → is-equiv (flanks.P {x} {y})
  P-is-equiv {x} {y} =
    iso→equiv (flanks.P {x} {y}) (flanks.P {x} {y}) P-invol P-invol .snd

  Q-is-equiv : ∀ {x y : ob} → is-equiv (flanks.Q {x} {y})
  Q-is-equiv {x} {y} =
    iso→equiv (flanks.Q {x} {y}) (flanks.Q {x} {y}) Q-invol Q-invol .snd

  P'-is-equiv : ∀ {x y : ob} → is-equiv (flanks.P' {x} {y})
  P'-is-equiv {x} {y} =
    iso→equiv (flanks.P' {x} {y}) (flanks.P' {x} {y}) P'-invol P'-invol .snd

  Q'-is-equiv : ∀ {x y : ob} → is-equiv (flanks.Q' {x} {y})
  Q'-is-equiv {x} {y} =
    iso→equiv (flanks.Q' {x} {y}) (flanks.Q' {x} {y}) Q'-invol Q'-invol .snd
```

Both cuts are function composition against a fixed endofunction, so
the two bracketings of a mixed word agree on the nose. Every edge is
thunkable and every edge is linear.

```agda
  all-thunkable : ∀ {w x : ob} (f : hom w x) → thunkable f
  all-thunkable f g h = refl

  all-linear : ∀ {y z : ob} (h : hom y z) → linear h
  all-linear h f g = refl
```

Every law in question is a path between edges, so one point of `Bool`
refutes it. These six readings send each law to an equation between
values.

```agda
  rb-point : readback-of → (m : Endo) (z : Bool) → b (m (a z)) ≡ m z
  rb-point R m z = happly (R m) z

  round-point : round-law → (m : Endo) (z : Bool)
              → b (a (m (b (a z)))) ≡ m z
  round-point W m z = happly (W m) z

  unitl⁻-point : unitl⁻-law → (g : Endo) (z : Bool) → g (b (a z)) ≡ g z
  unitl⁻-point U g z = happly (U g) z

  unitr⁺-point : unitr⁺-law → (f : Endo) (z : Bool) → b (a (f z)) ≡ f z
  unitr⁺-point U f z = happly (U f) z

  unitr⁻-point : unitr⁻-law → (f : Endo) (z : Bool) → a (b (f z)) ≡ f z
  unitr⁻-point U f z = happly (U f) z

  unitl⁺-point : unitl⁺-law → (g : Endo) (z : Bool) → g (a (b z)) ≡ g z
  unitl⁺-point U g z = happly (U g) z
```

## Both half-twists `not`

Each junction half-twist then cancels the flanking one. All four unit laws
hold, and the round law with them. Reflection at the axiom conjugates
by `not`, which moves the constant edge, so readback fails.

```agda
module not-not where
  open endo Bool.not Bool.not Bool.not.invol Bool.not.invol (λ _ → refl)
    public

  unitl⁻ : unitl⁻-law
  unitl⁻ g = funext λ z → ap g (Bool.not.invol z)

  unitr⁺ : unitr⁺-law
  unitr⁺ f = funext λ z → Bool.not.invol (f z)

  unitr⁻ : unitr⁻-law
  unitr⁻ f = funext λ z → Bool.not.invol (f z)

  unitl⁺ : unitl⁺-law
  unitl⁺ g = funext λ z → ap g (Bool.not.invol z)

  round : round-law
  round m = funext λ z →
    Bool.not.invol (m (Bool.not (Bool.not z))) ∙ ap m (Bool.not.invol z)

  no-readback : readback-of → ⊥
  no-readback R = true≢false (sym (rb-point R (λ _ → true) true))
```

## The negative half-twist `not`, the positive one the identity

Every hypothesis above still holds, and no unit law does: one flank of
each law survives as a single `not`. The round law fails at the
constant edge, and readback fails at the identity edge.

```agda
module not-id where
  open endo Bool.not (idfun Bool) Bool.not.invol (λ _ → refl) (λ _ → refl)
    public

  no-unitl⁻ : unitl⁻-law → ⊥
  no-unitl⁻ U = true≢false (sym (unitl⁻-point U (idfun Bool) true))

  no-unitr⁺ : unitr⁺-law → ⊥
  no-unitr⁺ U = true≢false (sym (unitr⁺-point U (idfun Bool) true))

  no-unitr⁻ : unitr⁻-law → ⊥
  no-unitr⁻ U = true≢false (sym (unitr⁻-point U (idfun Bool) true))

  no-unitl⁺ : unitl⁺-law → ⊥
  no-unitl⁺ U = true≢false (sym (unitl⁺-point U (idfun Bool) true))

  no-round : round-law → ⊥
  no-round W = true≢false (sym (round-point W (λ _ → true) true))

  no-readback : readback-of → ⊥
  no-readback R = true≢false (sym (rb-point R (idfun Bool) true))
```
