The two-element heap: one object, edges `Bool`, and the ternary
reflection `t ⊕ m ⊕ k`, which has no distinguished argument. Every
edge is neutral in the self-filled sense and both cuts are
represented, so either choice of origin extends the one carrier and
the one reflection to the full diagonal telescope — two unit
packages on the same graph, with the two hands always agreeing and
different compositions. What separates one edge from another is idempotence,
an equation and not an equivalence. Negation fixes the graph,
commutes with the reflection, and carries one origin to the other,
so no condition on `reflect` alone selects the origin: over this
reflection idempotence is not merely absent from the hypotheses but
inexpressible.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Bool.Heap where

open import Core.Type
open import Core.Base
open import Core.Data.Empty using (⊥; ¬_)
open import Core.Data.Sigma
open import Core.Data.Bool
open import Core.Kan using (_∙_)
open import Core.Path.Base using (_≢_)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv; iso→equiv)
open import Core.Function.Embedding
  using (is-embedding; injective→is-embedding; is-embedding→contr-fibers)
open import Core.HLevel.Base using (Π-is-hlevel)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (is-representable)
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Diagonal

open Bool using (xor; module xor)
```

## The carrier

Evaluating at any fixed pair of endpoints recovers the edge, so the
reflection is injective; the judgments form a set, so it is an
embedding and every represented judgment has a contractible fiber.

```agda
HB : virtual-graph 0ℓ 0ℓ
HB .virtual-graph.ob      = ⊤
HB .virtual-graph.hom _ _ = Bool
HB .virtual-graph.reflect m γ = xor (γ .fst .snd) (xor m (γ .snd .snd))

private
  emb : Bool → virtual-graph.argument HB tt tt → Bool
  emb m γ = xor (γ .fst .snd) (xor m (γ .snd .snd))

  emb-eval : ∀ m → emb m ((tt , false) , (tt , false)) ≡ m
  emb-eval m = xor.unitl (xor m false) ∙ xor.unitr m

  emb-lc : ∀ {m n} → emb m ≡ emb n → m ≡ n
  emb-lc {m} {n} p =
    sym (emb-eval m)
    ∙ ap (λ α → α ((tt , false) , (tt , false))) p
    ∙ emb-eval n

  emb-is-embedding : is-embedding emb
  emb-is-embedding =
    injective→is-embedding (Π-is-hlevel 2 λ _ → Bool.set) emb emb-lc
```

## Neutrality is free

Holding an edge in one slot and letting the other vary gives, on
the one hand, a doubled sum that the involution cancels, and on the
other a translation by `e ⊕ e`, which is zero. Neither computation
looks at which edge `e` is.

```agda
self : ∀ e → xor e e ≡ false
self e = sym (ap (xor e) (xor.unitr e)) ∙ xor.invol e false

left-neutral : ∀ e → is-equiv (λ (k : Bool) → xor e (xor e k))
left-neutral e =
  iso→equiv (λ k → xor e (xor e k)) (λ k → k)
    (xor.invol e) (xor.invol e) .snd

right-neutral : ∀ e → is-equiv (λ (g : Bool) → xor g (xor e e))
right-neutral e =
  iso→equiv (λ g → xor g (xor e e)) (λ g → g) absorbs absorbs .snd
  where
    absorbs : ∀ g → xor g (xor e e) ≡ g
    absorbs g = ap (xor g) (self e) ∙ xor.unitr g

every-edge-is-neutral : (e : Bool) → is-neutral HB {tt} e
every-edge-is-neutral e = left-neutral e , right-neutral e
```

## The diagonal telescope, at either origin

With an origin chosen the two cuts have one and the same
representative, the sum through that origin; readback holds at
either origin, since the group is 2-torsion. Both origins align
the same graph: `at false` and `at true` share `HB` and its one
reflection outright, and differ only in the diagonal data —
`rb`, `cut⁺`, `cut⁻`, and the unit package.

```agda
private
  cmp : Bool → Bool → Bool → Bool
  cmp o f g = xor f (xor o g)

  shape⁺
    : ∀ o f g (γ : virtual-graph.argument HB tt tt)
    → emb (cmp o f g) γ
    ≡ xor (γ .fst .snd) (xor f (xor o (xor g (γ .snd .snd))))
  shape⁺ o f g γ = ap (xor (γ .fst .snd))
    ( sym (xor.assoc f (xor o g) (γ .snd .snd))
    ∙ ap (xor f) (sym (xor.assoc o g (γ .snd .snd))) )

  shape⁻
    : ∀ o f g (γ : virtual-graph.argument HB tt tt)
    → emb (cmp o f g) γ
    ≡ xor (xor (γ .fst .snd) (xor f o)) (xor g (γ .snd .snd))
  shape⁻ o f g γ =
    ap (xor (γ .fst .snd))
      ( ap (λ b → xor b (γ .snd .snd)) (xor.assoc f o g)
      ∙ sym (xor.assoc (xor f o) g (γ .snd .snd)) )
    ∙ xor.assoc (γ .fst .snd) (xor f o) (xor g (γ .snd .snd))

rb : (o : Bool) → framing.readback-of HB (λ _ → o) (λ _ → o)
rb o m = ap (xor o) (xor.comm m o) ∙ xor.invol o m

cut⁺ : (o : Bool) → ∀ {x y z} (f g : Bool)
     → is-contr (is-representable HB (framing⁻.composite⁺ HB (λ _ → o) {x} {y} {z} f g))
cut⁺ o f g =
  is-embedding→contr-fibers emb-is-embedding
    (cmp o f g , funext (shape⁺ o f g))

cut⁻ : (o : Bool) → ∀ {x y z} (f g : Bool)
     → is-contr (is-representable HB (framing⁺.composite⁻ HB (λ _ → o) {x} {y} {z} f g))
cut⁻ o f g =
  is-embedding→contr-fibers emb-is-embedding
    (cmp o f g , funext (shape⁻ o f g))

module at (o : Bool) where
  open diagonal HB (λ _ → o) (rb o) (cut⁺ o) (cut⁻ o) public

  has-unit : (x : ⊤) → is-unital x
  has-unit _ = o , (left-neutral o , right-neutral o) , xor.invol o o

  open pinned has-unit public

  open framing HB (λ _ → o) (λ _ → o) using (composite⁺; composite⁻)

  full-cuts-agree : (f g : Bool) → composite⁺ f g ≡ composite⁻ f g
  full-cuts-agree f g = sym (reflect-⨾⁺ f g) ∙ reflect-⨾⁻ f g
```

## What the hypotheses fail to select

Idempotence is not implied: over the origin `false` the edge `true`
is a unit candidate whose self-composite is the origin instead of
itself. The two origins give two compositions on one graph and one
reflection.

```agda
private
  false≢true : false ≢ true
  false≢true p = subst (λ { false → ⊤ ; true → ⊥ }) p tt

rival-is-neutral : is-neutral HB {tt} true
rival-is-neutral = every-edge-is-neutral true

rival-not-idempotent : ¬ (at._⨾⁻_ false true true ≡ true)
rival-not-idempotent = false≢true

rival-not-the-unit : true ≢ at.idn false {tt}
rival-not-the-unit p = false≢true (sym p)

compositions-differ : at._⨾⁺_ false true true ≢ at._⨾⁺_ true true true
compositions-differ = false≢true
```

## The origins are exchanged by a half-twist

Negation fixes the graph and commutes with the reflection, and it
carries one origin's unit to the other's.

```agda
private
  half-twist : Bool → Bool
  half-twist = xor true

  half-twist-arg : virtual-graph.argument HB tt tt → virtual-graph.argument HB tt tt
  half-twist-arg γ = (γ .fst .fst , half-twist (γ .fst .snd))
              , (γ .snd .fst , half-twist (γ .snd .snd))

  half-twist-emb
    : ∀ t m k
    → xor (half-twist t) (xor (half-twist m) (half-twist k)) ≡ half-twist (xor t (xor m k))
  half-twist-emb true  true  true  = refl
  half-twist-emb true  true  false = refl
  half-twist-emb true  false true  = refl
  half-twist-emb true  false false = refl
  half-twist-emb false true  true  = refl
  half-twist-emb false true  false = refl
  half-twist-emb false false true  = refl
  half-twist-emb false false false = refl

reflection-is-equivariant
  : (m : Bool) (γ : virtual-graph.argument HB tt tt)
  → virtual-graph.reflect HB (half-twist m) (half-twist-arg γ)
  ≡ half-twist (virtual-graph.reflect HB m γ)
reflection-is-equivariant m γ = half-twist-emb (γ .fst .snd) m (γ .snd .snd)

half-twist-moves-the-origin : half-twist (at.idn false {tt}) ≡ at.idn true {tt}
half-twist-moves-the-origin = refl
```
