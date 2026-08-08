Four finite reader models bounding the associativity and cut
profiles. The projection model reflects every edge to the constant
judgment on itself: the tower theorems apply, `associates` computes
to an equation between distinct edges and fails everywhere, and the
same carrier carries readback with contractible cuts — so readback
does not derive `associates` — while the negative absorption
tier is refutable. The four-reader model is a full system on
`Bool × Bool` in which `associates π₁ g π₂` still fails: the
associativity classes are pinned to the two tier centres, one
thunkable edge and one linear edge, and its negative naturality
square fails at the coterm projection. The two remaining models carry
readback and both tiers while one cut has no representative — the
negative cut at the three-point carrier, the positive cut at the
reindexed four readers — so neither cut is derivable from the
cancellation data.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Bool.Readers where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false; module Bool)
open import Core.Data.Sum.Type using (_⊎_; inl; inr)
open import Core.Data.Sum.Properties using (⊎-is-hlevel)
open import Core.Data.Empty
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr; is-prop→is-set)
open import Core.HLevel.Base using (Π-is-hlevel; ×-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Naturality
open import Bb.VirtualGraphs.Degenerate.Interchange

is-true : Bool → Type
is-true true  = ⊤
is-true false = ⊥
```

## The projection model

One object, edges the booleans, and a reflection that ignores its
argument. A judgment reads off its edge at any argument, so
reflection is injective and the embedding condition holds over the
hom set. Each composite judgment collapses to the constant judgment on
one factor, and that factor represents it on the nose.

```agda
module projection where

  P : virtual-graph 0ℓ 0ℓ
  P .virtual-graph.ob      = ⊤
  P .virtual-graph.hom _ _ = Bool
  P .virtual-graph.reflect m _ = m

  emb : (α : virtual-graph.judgment P tt tt) → is-prop (is-representable P α)
  emb = injective→is-embedding (Π-is-hlevel 2 λ _ → Bool.set)
          (virtual-graph.reflect P)
          (λ w → happly w ((tt , false) , (tt , false)))

  S : reflect-is-embedding P
  S α = emb α

  C⁺ : framing⁻.is-composable⁺ P (λ _ → false)
  C⁺ f g = f , refl

  C⁻ : framing⁺.is-composable⁻ P (λ _ → false)
  C⁻ f g = g , refl

  open transfer P (λ _ → false) (λ _ → false) S C⁺ C⁻
```

With both hands projections, `associates f g h` is `h ≡ f`, and any
distinct pair refutes it. The two universal closures die at every
edge, and a centre of the `⁻` fiber would read constantly as the
identity of the coterm family, which two coterms already refute.

```agda
  no-associates : ∀ g → associates true g false → ⊥
  no-associates g w = subst is-true (sym w) tt

  no-thunkable : ∀ f → thunkable f → ⊥
  no-thunkable false T = subst is-true (T true true) tt
  no-thunkable true  T = subst is-true (sym (T true false)) tt

  no-linear : ∀ h → linear h → ⊥
  no-linear false L = subst is-true (sym (L true true)) tt
  no-linear true  L = subst is-true (L false false) tt

  no-absorbing⁻ : absorbing⁻.is-absorbing⁻ P (λ _ → false) → ⊥
  no-absorbing⁻ I =
    subst is-true
      ( sym (happly (I tt .center .snd) (tt , true))
      ∙ happly (I tt .center .snd) (tt , false) )
      tt
```

The same carrier satisfies the framed telescope: the axiom reads
back the edge by definition and both cuts are contractible over the
embedding, so the frame proves its unit laws and mixed associativity
while `associates` still fails.

```agda
  module R = framed-interchange P (λ _ → false) (λ _ → false)
    (λ _ → refl)
    (λ f g → prop-inhabited→is-contr (emb _) (f , refl))
    (λ f g → prop-inhabited→is-contr (emb _) (g , refl))

  no-associates-readback
    : ∀ g → (true R.⨾⁺ g) R.⨾⁻ false ≡ true R.⨾⁺ (g R.⨾⁻ false) → ⊥
  no-associates-readback g w = subst is-true (sym w) tt
```

## The four readers

Edges are pairs of booleans, read as functions of the argument: a
`false` first component is a projection onto one flank (`π₁` the
term flank, `π₂` the coterm flank), a `true` first component a
constant at the projection its second component names. One probe
argument with a constant in both flanks separates the four readers,
so reflection is injective.

```agda
module four-reader where

  M : Type
  M = Bool × Bool

  π₁ π₂ κ₁ κ₂ : M
  π₁ = false , false
  π₂ = false , true
  κ₁ = true , false
  κ₂ = true , true

  M-set : is-set M
  M-set = ×-is-hlevel 2 Bool.set Bool.set

  rf : M → Sigma ⊤ (λ _ → M) × Sigma ⊤ (λ _ → M) → M
  rf (false , false) γ = γ .fst .snd
  rf (false , true)  γ = γ .snd .snd
  rf (true  , d)     γ = false , d

  flag₁ flag₂ : M → Type
  flag₁ v = is-true (v .fst)
  flag₂ v = is-true (v .snd)

  probe : Sigma ⊤ (λ _ → M) × Sigma ⊤ (λ _ → M)
  probe = (tt , κ₁) , (tt , κ₂)

  flip₁ : M → M
  flip₁ (false , d) = true  , d
  flip₁ (true  , d) = false , d

  flip₁-rf : ∀ m → flip₁ (rf m probe) ≡ m
  flip₁-rf (false , false) = refl
  flip₁-rf (false , true)  = refl
  flip₁-rf (true  , d)     = refl

  rf-inj : {m n : M} → rf m ≡ rf n → m ≡ n
  rf-inj {m} {n} w = sym (flip₁-rf m) ∙ ap flip₁ (happly w probe) ∙ flip₁-rf n
```

Both half-twists are the term projection `π₁`. Each composite judgment
computes to a reader again, so a case split represents both cuts,
and the projection onto each side inhabits that side's tier: the
`⁻` centre is `π₂` and the `⁺` centre is `π₁`.

```agda
  model : virtual-graph 0ℓ 0ℓ
  model .virtual-graph.ob      = ⊤
  model .virtual-graph.hom _ _ = M
  model .virtual-graph.reflect = rf

  open framing model (λ _ → π₁) (λ _ → π₁)
    using (coact-π; act-π; is-natural⁻)

  S : reflect-is-embedding model
  S α = injective→is-embedding (Π-is-hlevel 2 λ _ → M-set) rf rf-inj α

  C⁺ : framing⁻.is-composable⁺ model (λ _ → π₁)
  C⁺ (false , false) g = π₁ , refl
  C⁺ (false , true) (false , false) = κ₁ , refl
  C⁺ (false , true) (false , true)  = π₂ , refl
  C⁺ (false , true) (true , d) = (true , d) , refl
  C⁺ (true , d) g = (true , d) , refl

  C⁻ : framing⁺.is-composable⁻ model (λ _ → π₁)
  C⁻ f (false , true) = π₂ , refl
  C⁻ f (true , d) = (true , d) , refl
  C⁻ (false , false) (false , false) = π₁ , refl
  C⁻ (false , true)  (false , false) = κ₁ , refl
  C⁻ (true , d)      (false , false) = (true , d) , refl

  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ .center = π₂ , refl
  tier⁻ .paths ((false , true) , w) i =
    π₂ , Π-is-hlevel 2 (λ _ → M-set) (coact-π π₂) snd refl w i
  tier⁻ .paths ((false , false) , w) =
    ex-falso (subst flag₂ (sym (happly w (tt , π₂))) tt)
  tier⁻ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , (true , d)))) tt)

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ .center = π₁ , refl
  tier⁺ .paths ((false , false) , w) i =
    π₁ , Π-is-hlevel 2 (λ _ → M-set) (act-π π₁) snd refl w i
  tier⁺ .paths ((false , true) , w) =
    ex-falso (subst flag₂ (sym (happly w (tt , π₂))) tt)
  tier⁺ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , (true , d)))) tt)
```

`associates π₁ g π₂` computes to `π₂ ≡ π₁` for every middle edge:
the left bracketing ends in the coterm projection, the right one in
the term projection. The classes are exactly the centres — `π₂`
associates ahead of every pair, `π₁` behind every pair, and the
remaining six closures each die on a computed instance. The linear
edge `π₁` is both half-twists, so the framing itself is linear and not
thunkable.

```agda
  open transfer model (λ _ → π₁) (λ _ → π₁) S C⁺ C⁻

  no-associates : ∀ g → associates π₁ g π₂ → ⊥
  no-associates g w = subst flag₂ w tt

  centre⁻-thunkable : thunkable π₂
  centre⁻-thunkable g (false , true) = refl
  centre⁻-thunkable g (true , d) = refl
  centre⁻-thunkable (false , false) (false , false) = refl
  centre⁻-thunkable (false , true)  (false , false) = refl
  centre⁻-thunkable (true , e)      (false , false) = refl

  centre⁺-linear : linear π₁
  centre⁺-linear (false , false) g = refl
  centre⁺-linear (false , true) (false , false) = refl
  centre⁺-linear (false , true) (false , true)  = refl
  centre⁺-linear (false , true) (true , e) = refl
  centre⁺-linear (true , d) g = refl

  no-thunkable-half-twist : thunkable π₁ → ⊥
  no-thunkable-half-twist T = subst flag₂ (T π₁ π₂) tt

  no-thunkable-κ : ∀ d → thunkable (true , d) → ⊥
  no-thunkable-κ d T = subst flag₁ (sym (T π₁ π₂)) tt

  no-linear-centre⁻ : linear π₂ → ⊥
  no-linear-centre⁻ L = subst flag₂ (L π₁ π₁) tt

  no-linear-κ : ∀ d → linear (true , d) → ⊥
  no-linear-κ d L = subst flag₁ (L π₁ π₁) tt
```

Both half-twists are the term projection, and the negative hand reads that
half-twist differently on its two sides: on the left it returns the edge,
on the right a constant. So the negative naturality square fails at
the coterm projection, and the negative tier fails with it, over a
carrier that already satisfies the embedding condition, both cuts, and
both absorption tiers.

```agda
  cross-values : (π₁ ⨾⁻ π₂ ≡ π₂) × (π₂ ⨾⁻ π₁ ≡ κ₁)
  cross-values = refl , refl

  no-nat⁻ : nat⁻-law → ⊥
  no-nat⁻ N = subst flag₁ (sym (N π₂)) tt

  no-natural⁻ : is-natural⁻ → ⊥
  no-natural⁻ N = no-nat⁻ (nat⁻ N)
```

## The three-point carrier

The projection model with one added reading point: constants read
constantly as themselves, and the added point — the half-twist in both
slots — reads whichever flank holds the half-twist, and the coterm where
both flanks are constant. Readback and both tiers hold; the
negative cut has no representative, since a constant against the
half-twist is a mixed reader the three-point carrier does not hold.

```agda
module attempt₁ where

  E : Type
  E = Bool ⊎ ⊤

  ⋆ : E
  ⋆ = inr tt

  is-inl : E → Type
  is-inl (inl _) = ⊤
  is-inl (inr _) = ⊥

  tflag : E → Type
  tflag (inl true)  = ⊤
  tflag (inl false) = ⊥
  tflag (inr _)     = ⊥

  E-set : is-set E
  E-set = ⊎-is-hlevel 0 Bool.set (is-prop→is-set (λ _ _ → refl))

  P₁ : virtual-graph 0ℓ 0ℓ
  P₁ .virtual-graph.ob      = ⊤
  P₁ .virtual-graph.hom _ _ = E
  P₁ .virtual-graph.reflect (inl m) γ = inl m
  P₁ .virtual-graph.reflect (inr t) ((_ , inr _) , (_ , k)) = k
  P₁ .virtual-graph.reflect (inr t) ((_ , inl m) , (_ , inr _)) = inl m
  P₁ .virtual-graph.reflect (inr t) ((_ , inl m) , (_ , inl n)) = inl n

  open framing P₁ (λ _ → ⋆) (λ _ → ⋆) using (coact-π; act-π; composite⁻)

  rb : framing.readback-of P₁ (λ _ → ⋆) (λ _ → ⋆)
  rb (inl m) = refl
  rb (inr t) = refl

  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ .center = ⋆ , refl
  tier⁻ .paths (inr t , w) i =
    ⋆ , Π-is-hlevel 2 (λ _ → E-set) (coact-π ⋆) snd refl w i
  tier⁻ .paths (inl m , w) =
    ex-falso (subst is-inl (happly w (tt , ⋆)) tt)

  act-π-⋆ : (t : Sigma ⊤ (λ _ → E)) → act-π ⋆ t ≡ t .snd
  act-π-⋆ (_ , inl m) = refl
  act-π-⋆ (_ , inr t) = refl

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ .center = ⋆ , funext act-π-⋆
  tier⁺ .paths (inr t , w) i =
    ⋆ , Π-is-hlevel 2 (λ _ → E-set) (act-π ⋆) snd (funext act-π-⋆) w i
  tier⁺ .paths (inl m , w) =
    ex-falso (subst is-inl (happly w (tt , ⋆)) tt)

  no-cut⁻ : is-representable P₁ (composite⁻ (inl false) ⋆) → ⊥
  no-cut⁻ (inl x , w) =
    subst tflag
      ( sym (happly w ((tt , ⋆) , (tt , inl true)))
      ∙ happly w ((tt , ⋆) , (tt , inl false)) )
      tt
  no-cut⁻ (inr t , w) =
    subst is-inl (sym (happly w ((tt , ⋆) , (tt , ⋆)))) tt
```

## The four readers, reindexed

Constants reindexed to themselves and the positive half-twist moved to
the coterm projection: every edge reads back as itself, and each
tier's centre is the other half-twist — the cancellation situation on the
nose. The positive cut has no representative: the coterm projection
against the term projection composes to the reader constantly at
`π₁`, and readback pins every constant reader to its own value, so
no edge reads constantly at a projection.

```agda
module attempt₂ where

  open four-reader using (M; π₁; π₂; κ₁; M-set; flag₁)

  Q : virtual-graph 0ℓ 0ℓ
  Q .virtual-graph.ob      = ⊤
  Q .virtual-graph.hom _ _ = M
  Q .virtual-graph.reflect (false , false) γ = γ .fst .snd
  Q .virtual-graph.reflect (false , true)  γ = γ .snd .snd
  Q .virtual-graph.reflect (true , d)      γ = true , d

  open framing Q (λ _ → π₁) (λ _ → π₂) using (coact-π; act-π; composite⁺)

  rb : framing.readback-of Q (λ _ → π₁) (λ _ → π₂)
  rb (false , false) = refl
  rb (false , true)  = refl
  rb (true , d)      = refl

  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ .center = π₂ , refl
  tier⁻ .paths ((false , true) , w) i =
    π₂ , Π-is-hlevel 2 (λ _ → M-set) (coact-π π₂) snd refl w i
  tier⁻ .paths ((false , false) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , κ₁))) tt)
  tier⁻ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (happly w (tt , π₁)) tt)

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ .center = π₁ , refl
  tier⁺ .paths ((false , false) , w) i =
    π₁ , Π-is-hlevel 2 (λ _ → M-set) (act-π π₁) snd refl w i
  tier⁺ .paths ((false , true) , w) =
    ex-falso (subst flag₁ (sym (happly w (tt , κ₁))) tt)
  tier⁺ .paths ((true , d) , w) =
    ex-falso (subst flag₁ (happly w (tt , π₁)) tt)

  no-cut⁺ : is-representable Q (composite⁺ π₂ π₁) → ⊥
  no-cut⁺ ((false , false) , w) =
    subst flag₁ (happly w ((tt , κ₁) , (tt , κ₁))) tt
  no-cut⁺ ((false , true) , w) =
    subst flag₁ (happly w ((tt , κ₁) , (tt , κ₁))) tt
  no-cut⁺ ((true , d) , w) =
    subst flag₁ (happly w ((tt , κ₁) , (tt , κ₁))) tt
```
