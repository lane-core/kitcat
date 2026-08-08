The word model: one object, canonical descriptors as edges, and the
sandwich reflection that surrounds an edge with its argument — the
coterm half composing on the inside, the term half through `φ` on the
outside. The negative half-twist is the unit translation `τ̂`, the positive
half-twist the identity descriptor `ε̂`, and readback is the sandwich
collapse, since `φW τ̂` computes to `ε̂`.

Stability comes from the hom sets: evaluating a reflection sandwiches
the edge between the two half-twists, and the unit laws make that injective.
Both cuts are representable — `comp` for the positive, `cut⁻` for the
negative — and each absorption tier's fiber contracts at its own
half-twist.

The descriptor shift `t ∸ length p` is a ℤ-grading: additive for the
positive cut, decremented by `φ`, and onto. The `associates` triple
`(τ̂ , ε̂ , ε̂)` is empty, so `τ̂` is not thunkable and `ε̂` is not
linear. The double half-twist inverts `τ̂` on one side only, and the two
half-twists are distinct edges.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Word.Model where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat
open import Core.Data.List
open import Core.Data.Bool
open import Core.Data.Int
open import Core.HLevel.Base using (Π-is-hlevel)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Word.Carrier

open Nat using (_+_; _-_; _==ᵇ_; ==ᵇ-sound; monus-max)
open List using (length)
open Bool using (So)
open Int using (add; zpred; add-pred; _⊖_; ⊖-pred; ⊖-hom; ⊖-balance; zero-l)
```

## The instance

```agda
BW : virtual-graph 0ℓ 0ℓ
BW .virtual-graph.ob = ⊤
BW .virtual-graph.hom _ _ = W
BW .virtual-graph.reflect f γ =
  comp (comp (φW (γ .fst .snd)) f) (γ .snd .snd)

open virtual-graph BW using (ob; hom; term; coterm; judgment; reflect)
open framing BW (λ _ → τ̂) (λ _ → ε̂)
  using ( var; covar; coact-π; act-π; coact; act; eval
        ; composite⁺; composite⁻; embedding-from-hom-sets )
```

Readback is the sandwich collapse: the term flank of the axiom is
`φW τ̂`, which is the identity descriptor, and the coterm flank is the
identity descriptor itself.

```agda
BW-readback : framing.readback-of BW (λ _ → τ̂) (λ _ → ε̂)
BW-readback f = sandwich f
```

## Stability

Evaluating a reflection sandwiches an edge between the two half-twists, so it
is injective by the unit laws; with `W` a set this makes `reflect` an
embedding at every pair of objects.

```agda
BW-embedding : reflect-is-embedding BW
BW-embedding =
  embedding-from-hom-sets (λ {x} {y} → W-set)
    (λ {x} {y} {m} {n} p → sym (sandwich m) ∙ p ∙ sandwich n)
```

## Both cuts are representable

The candidate representatives are `comp` and `cut⁻`; each reflects to
its composite judgment pointwise, through the three semantic laws of
`φ`.

```agda
cut⁺-path : ∀ a f g b n
  → evW (comp (comp (φW a) (comp f g)) b) n
  ≡ evW (comp (comp (φW a) f) (comp (comp ε̂ g) b)) n
cut⁺-path a f g b n =
    ev-comp (comp (φW a) (comp f g)) b n
  ∙ ev-comp (φW a) (comp f g) (evW b n)
  ∙ ap (evW (φW a)) (ev-comp f g (evW b n))
  ∙ ap (λ m → evW (φW a) (evW f m)) (sym step-r)
  ∙ sym (ev-comp (φW a) f (evW (comp (comp ε̂ g) b) n))
  ∙ sym (ev-comp (comp (φW a) f) (comp (comp ε̂ g) b) n)
  where
    step-r : evW (comp (comp ε̂ g) b) n ≡ evW g (evW b n)
    step-r = ap (λ u → evW (comp u b) n) (comp-unitl g) ∙ ev-comp g b n

ρ⁺ : ∀ f g → reflect (comp f g) ≡ composite⁺ f g
ρ⁺ f g = funext λ γ →
  ev-inj (comp (comp (φW (γ .fst .snd)) (comp f g)) (γ .snd .snd))
         (comp (comp (φW (γ .fst .snd)) f)
               (comp (comp ε̂ g) (γ .snd .snd)))
         (cut⁺-path (γ .fst .snd) f g (γ .snd .snd))

φ-two : ∀ a f m → φ (evW a) (φ (evW f) m)
                ≡ φ (evW (comp (comp (φW a) f) ε̂)) m
φ-two a f Z     = refl
φ-two a f (S m) = sym
  ( ev-comp (comp (φW a) f) ε̂ m
  ∙ ev-comp (φW a) f (m + Z)
  ∙ ev-φ a (evW f (m + Z))
  ∙ ap (λ k → φ (evW a) (evW f k)) (Nat.add.unitr m) )

cut⁻-path : ∀ a f g b n
  → evW (comp (comp (φW a) (cut⁻ f g)) b) n
  ≡ evW (comp (comp (φW (comp (comp (φW a) f) ε̂)) g) b) n
cut⁻-path a f g b n =
    ev-comp (comp (φW a) (cut⁻ f g)) b n
  ∙ ev-comp (φW a) (cut⁻ f g) (evW b n)
  ∙ ap (evW (φW a)) (ev-comp (φW f) g (evW b n))
  ∙ ap (evW (φW a)) (ev-φ f (evW g (evW b n)))
  ∙ ev-φ a (φ (evW f) (evW g (evW b n)))
  ∙ φ-two a f (evW g (evW b n))
  ∙ sym (ev-φ (comp (comp (φW a) f) ε̂) (evW g (evW b n)))
  ∙ sym (ev-comp (φW (comp (comp (φW a) f) ε̂)) g (evW b n))
  ∙ sym (ev-comp (comp (φW (comp (comp (φW a) f) ε̂)) g) b n)

ρ⁻ : ∀ f g → reflect (cut⁻ f g) ≡ composite⁻ f g
ρ⁻ f g = funext λ γ →
  ev-inj (comp (comp (φW (γ .fst .snd)) (cut⁻ f g)) (γ .snd .snd))
         (comp (comp (φW (comp (comp (φW (γ .fst .snd)) f) ε̂)) g)
               (γ .snd .snd))
         (cut⁻-path (γ .fst .snd) f g (γ .snd .snd))

BW-comp⁺ : framing⁻.is-composable⁺ BW (λ _ → τ̂)
BW-comp⁺ f g = comp f g , ρ⁺ f g

BW-comp⁻ : framing⁺.is-composable⁻ BW (λ _ → ε̂)
BW-comp⁻ f g = cut⁻ f g , ρ⁻ f g
```

Stability makes each cut's fiber contractible.

```agda
BW-contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
          → is-contr (is-representable BW (composite⁺ {x} {y} {z} f g))
BW-contr⁺ f g =
  contr-from-embedding BW BW-embedding (composite⁺ f g) (comp f g , ρ⁺ f g)

BW-contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
          → is-contr (is-representable BW (composite⁻ {x} {y} {z} f g))
BW-contr⁻ f g =
  contr-from-embedding BW BW-embedding (composite⁻ f g) (cut⁻ f g , ρ⁻ f g)
```

## The framing is absorbing

Each fiber has the expected half-twist as centre, and any inhabitant is
pinned to it by evaluating the fiber path at the other half-twist's axiom
half; the path component lives in a set-valued function type, so it
rides along as a proposition.

```agda
Π⁻-set : is-set ((γ : coterm tt) → W)
Π⁻-set = Π-is-hlevel (S (S Z)) (λ _ → W-set)

Π⁺-set : is-set ((t : term tt) → W)
Π⁺-set = Π-is-hlevel (S (S Z)) (λ _ → W-set)

coactε : coact-π {tt} {tt} ε̂ ≡ snd
coactε = funext λ γ → comp-unitl (γ .snd)

actτ : act-π {tt} {tt} τ̂ ≡ snd
actτ = funext λ t → act-τ (t .snd)

q⁻ : (e : W) → coact-π {tt} {tt} e ≡ snd → ε̂ ≡ e
q⁻ e pe = sym (sym (sandwich e) ∙ happly pe (tt , ε̂))

q⁺ : (e : W) → act-π {tt} {tt} e ≡ snd → τ̂ ≡ e
q⁺ e pe = sym (sym (sandwich e) ∙ happly pe (tt , τ̂))

BW-absorbing⁻ : absorbing⁻.is-absorbing⁻ BW (λ _ → τ̂)
BW-absorbing⁻ x .center = ε̂ , coactε
BW-absorbing⁻ x .paths (e , pe) i =
  q⁻ e pe i
  , is-prop→PathP (λ j → Π⁻-set (coact-π (q⁻ e pe j)) snd) coactε pe i

BW-absorbing⁺ : absorbing⁺.is-absorbing⁺ BW (λ _ → ε̂)
BW-absorbing⁺ x .center = τ̂ , actτ
BW-absorbing⁺ x .paths (e , pe) i =
  q⁺ e pe i
  , is-prop→PathP (λ j → Π⁺-set (act-π (q⁺ e pe j)) snd) actτ pe i
```

## The tower

Chosen representatives for both cuts, with the two hands' words written
through `tower`.

```agda
open tower BW (λ _ → τ̂) (λ _ → ε̂) BW-embedding BW-comp⁺ BW-comp⁻
  using (_⨾⁺_; _⨾⁻_; associates; thunkable; linear)
```

## The winding grade

The shift of a descriptor is its eventual translation defect
`t ∸ length p` as an integer. Trim preserves it, the positive cut adds
it, and `φ` decrements it: the ℤ-grading, with winding `1 − 2·shift`
and the double half-twist the `+1` winding generator. Every grade is
inhabited.

```agda
shift : W → Int
shift A = A .snd .fst ⊖ length (A .fst)

tab-len : ∀ N (g : Nat → Nat) → length (tabulate N g) ≡ N
tab-len Z     g = refl
tab-len (S M) g = ap S (tab-len M (λ k → g (S k)))

pop-shift : ∀ x t' b → (So b → S x ≡ t')
  → (trim-pop x t' b .snd ⊖ length (trim-pop x t' b .fst)) ≡ (t' ⊖ S Z)
pop-shift x t' false h = refl
pop-shift x t' true  h = ap (_⊖ S Z) (h tt)

step-shift : ∀ x q t'
  → (trim-step x (q , t') .snd ⊖ length (trim-step x (q , t') .fst))
  ≡ (t' ⊖ S (length q))
step-shift x []      t' = pop-shift x t' (S x ==ᵇ t') (==ᵇ-sound (S x) t')
step-shift x (y ∷ q) t' = refl

trim-shift : ∀ p t
  → (trim p t .snd ⊖ length (trim p t .fst)) ≡ (t ⊖ length p)
trim-shift []      t = refl
trim-shift (x ∷ p) t =
    step-shift x (trim p t .fst) (trim p t .snd)
  ∙ ⊖-pred (trim p t .snd) (length (trim p t .fst))
  ∙ ap zpred (trim-shift p t)
  ∙ sym (⊖-pred t (length p))

gN-val : ∀ A B → gW A B (onset A B)
       ≡ ((B .snd .fst - length (A .fst)) + A .snd .fst)
gN-val A B =
  ap (evW A)
     ( ev-past (B .fst) (B .snd .fst) (length (A .fst) - B .snd .fst)
     ∙ monus-max (length (A .fst)) (B .snd .fst)
     ∙ Nat.max.comm (length (A .fst)) (B .snd .fst)
     ∙ sym (monus-max (B .snd .fst) (length (A .fst)))
     ∙ Nat.add.comm (B .snd .fst - length (A .fst)) (length (A .fst)) )
  ∙ ev-past (A .fst) (A .snd .fst) (B .snd .fst - length (A .fst))

shift-⨾⁺ : ∀ A B → shift (A ⨾⁺ B) ≡ add (shift A) (shift B)
shift-⨾⁺ A B =
    trim-shift (tabulate (onset A B) (gW A B)) (gW A B (onset A B))
  ∙ ap (gW A B (onset A B) ⊖_) (tab-len (onset A B) (gW A B))
  ∙ ap (_⊖ onset A B) (gN-val A B)
  ∙ ⊖-balance ((tB - lA) + tA) (onset A B) (tA + tB) (lA + lB) bal
  ∙ sym (⊖-hom tA lA tB lB)
  where
    lA = length (A .fst)
    tA = A .snd .fst
    lB = length (B .fst)
    tB = B .snd .fst

    bal : ((tB - lA) + tA) + (lA + lB) ≡ ((tA + tB) + (lB + (lA - tB)))
    bal =
        ap (_+ (lA + lB)) (Nat.add.comm (tB - lA) tA)
      ∙ sym (Nat.add.assoc tA (tB - lA) (lA + lB))
      ∙ ap (tA +_) (Nat.add.assoc (tB - lA) lA lB)
      ∙ ap (λ w → tA + (w + lB)) (monus-max tB lA)
      ∙ sym ( sym (Nat.add.assoc tA tB (lB + (lA - tB)))
            ∙ ap (tA +_) (Nat.add.assoc tB lB (lA - tB))
            ∙ ap (λ w → tA + (w + (lA - tB))) (Nat.add.comm tB lB)
            ∙ ap (tA +_) (sym (Nat.add.assoc lB tB (lA - tB)))
            ∙ ap (λ w → tA + (lB + w)) (Nat.add.comm tB (lA - tB))
            ∙ ap (λ w → tA + (lB + w)) (monus-max lA tB)
            ∙ ap (λ w → tA + (lB + w)) (Nat.max.comm lA tB)
            ∙ ap (tA +_) (Nat.add.comm lB (Nat.max tB lA)) )

shift-φ : ∀ A → shift (φW A) ≡ zpred (shift A)
shift-φ ([] , Z , c)       = refl
shift-φ ([] , S Z , c)     = refl
shift-φ ([] , S (S u) , c) = refl
shift-φ (x ∷ p , t , c)    = ⊖-pred t (S (length p))

shift-⨾⁻ : ∀ A B → shift (A ⨾⁻ B) ≡ zpred (add (shift A) (shift B))
shift-⨾⁻ A B =
    shift-⨾⁺ (φW A) B
  ∙ ap (λ z → add z (shift B)) (shift-φ A)
  ∙ add-pred (shift A) (shift B)

zeros : Nat → List Nat
zeros Z     = []
zeros (S n) = Z ∷ zeros n

zeros-can : ∀ n → So (can? (Z ∷ zeros n) Z)
zeros-can Z     = tt
zeros-can (S n) = zeros-can n

zeros-len : ∀ n → length (zeros n) ≡ n
zeros-len Z     = refl
zeros-len (S n) = ap S (zeros-len n)

shift-onto : ∀ z → Σ A ∶ W , shift A ≡ z
shift-onto (pos n)    = ([] , n , tt) , refl
shift-onto (negsuc n) = (Z ∷ zeros n , Z , zeros-can n)
                      , λ i → Z ⊖ S (zeros-len n i)
```

## The measurements

The `associates` triple `(τ̂ , ε̂ , ε̂)` computes to `ε̂` on the left
bracketing and to the descriptor `([1] , 1)` on the right, so mixed
words do not reassociate; in particular the negative half-twist is not
thunkable and the identity is not linear. The double half-twist kills the
negative half-twist on one side only, and the half-twists are distinct.

```agda
w-nil : W → Type
w-nil A = nil? (A .fst)

pos? : Nat → Type
pos? Z     = ⊥
pos? (S _) = ⊤

associates-refuted : ¬ associates τ̂ ε̂ ε̂
associates-refuted e = subst w-nil e tt

thunkable-refuted : ¬ thunkable τ̂
thunkable-refuted th = associates-refuted (th ε̂ ε̂)

linear-refuted : ¬ linear ε̂
linear-refuted li = associates-refuted (li τ̂ ε̂)

bicyclic-collapse : (δ̂ ⨾⁺ τ̂) ≡ ε̂
bicyclic-collapse = refl

bicyclic-persists : ¬ ((τ̂ ⨾⁺ δ̂) ≡ ε̂)
bicyclic-persists e = subst w-nil (sym e) tt

half-twist-distinct : ¬ (τ̂ ≡ ε̂)
half-twist-distinct e = subst (λ A → pos? (A .snd .fst)) e tt
```
