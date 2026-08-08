The recognition apparatus instantiated at the word model: the
readback-plus-clauses type, the per-object shape, and the cross-pair
grammar.

The judgments here form a set, so each clause is a proposition.
Candidate readback already pins the candidate. So the
readback-plus-clauses type contracts, with the clauses riding along.
The candidate `(ω̂ , ε̂)`, which carries both clauses, fails readback.

The per-object shape holds at the half-twist pair. Its sandwich clause alone
pins. Read as candidate readback it returns the half-twist pair, so the
recognition type contracts, the framing type is a proposition, and the
whole recognition record is one. The recognized cuts are the descriptor
compositions on the nose. Every witness induces the same cut edges, and
the withheld word still fails to associate over them.

The cross-pair grammar holds at the half-twist pair as well. Each gluing
clause follows because an adjacent sandwich pins its own pair first,
and the mixed-pair argument recovers the same pinning. Every clause of
the predicate is a proposition here, so the cross-pair type
contracts.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Word.Recognition where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty using (¬_)
open import Core.Data.Nat
open import Core.Data.List
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.HLevel.Base
  using (Π-is-prop; Πi-is-prop; is-prop-×; Σ-prop-path; Π-is-hlevel)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Recognition
open import Bb.VirtualGraphs.Mediation using (module at-framing)
open import Bb.VirtualGraphs.Degenerate.Shape
open import Bb.VirtualGraphs.Degenerate.Gluing
open import Bb.VirtualGraphs.Word.Carrier
open import Bb.VirtualGraphs.Word.Model
open import Bb.VirtualGraphs.Word.Mediation using (half-twists)
open import Bb.VirtualGraphs.Word.Census
  using (frame-at; half-twist-frame; rb-half-twists; rb-pins; pair-path; half-twists-inv; ω̂)
open import Bb.VirtualGraphs.Word.Census as Census using (module recognize)

open candidate BW using (frame; rb)

open shape BW
  using ( pair; flanks; is-half-twist; is-framed; frame-of; rx-of; corx-of
        ; cuts; is-deductive-system-depreciated; deductive-prop )

open grammar BW
  using (cross; sand; is-cross; glue⁻; glue⁺; pred; module play)

open at-framing BW (λ _ → τ̂) (λ _ → ε̂) BW-embedding BW-comp⁺ BW-comp⁻
  using (tf; law₀; law₁; to₀; to₁)
```

## The judgments form a set

```agda
jset : ∀ {x y} → is-set (virtual-graph.judgment BW x y)
jset = Π-is-hlevel (S (S Z)) λ _ → W-set
```

## Readback with the clauses

Readback returns the half-twist pair, so the candidate that carries both
clauses without being the half-twist pair fails it: the pinning would empty
its descriptor list.

```agda
impostor : frame
impostor = frame-at ω̂ ε̂

impostor-no-rb : ¬ rb impostor
impostor-no-rb R = subst w-nil (sym (recognize.pin-a impostor R)) tt
```

The two clauses hold at the framing, since the two edge-level equations
do.

```agda
laws : (x : ⊤) → law₀ x × law₁ x
laws _ = half-twists

mediates-tf : selects BW tf
mediates-tf x = to₀ x (laws x .fst) , to₁ x (laws x .snd)
```

Each clause is an equation between judgments, so it is a proposition
here. Readback pins the candidate, and the conjunction contracts.

```agda
selects-is-prop : (q : frame) → is-prop (selects BW q)
selects-is-prop q =
  Π-is-prop (clause.mediates-is-prop BW q λ α β → jset α β)

factor-is-prop : (q : frame) → is-prop (rb q × selects BW q)
factor-is-prop q = is-prop-× (Census.rb-is-prop q) (selects-is-prop q)

pinned-contr : is-contr (pinned BW)
pinned-contr .center = tf , (rb-half-twists , mediates-tf)
pinned-contr .paths (q , R , M) =
  sym (Σ-prop-path factor-is-prop (rb-pins q R))
```

## The per-object shape

The recognized pair is the half-twist pair, and the sandwich clause is the
model's own collapse. The two fibers are the ones candidate
invertibility computes there. Both cuts are representable with a
contractible fiber, so the shape carries the whole recognition
record.

```agda
half-twist-pair : pair tt
half-twist-pair = τ̂ , ε̂

flanksᵂ : flanks half-twist-pair
flanksᵂ f = sandwich f

half-twistᵂ : is-half-twist half-twist-pair
half-twistᵂ = flanksᵂ , half-twists-inv

framedᵂ : is-framed
framedᵂ _ = half-twist-pair , half-twistᵂ

cutsᵂ : cuts framedᵂ
cutsᵂ = (λ f g → BW-contr⁺ f g) , (λ f g → BW-contr⁻ f g)

deductiveᵂ : is-deductive-system-depreciated
deductiveᵂ = BW-embedding , framedᵂ , cutsᵂ
```

At the one object the diagonal sandwich is the whole of candidate
readback, so the sandwich alone pins the pair. Each clause of the
condition is a proposition here. So the recognition type contracts, the
framing type is a proposition, and the record is one with it.

```agda
to-rb : (p : pair tt) → flanks p → rb (frame-at (p .fst) (p .snd))
to-rb p F f = F f

pins : (p : pair tt) → flanks p → p ≡ half-twist-pair
pins p F = pair-path (frame-at (p .fst) (p .snd)) (to-rb p F)

is-half-twist-propᵂ : (p : pair tt) → is-prop (is-half-twist p)
is-half-twist-propᵂ p = is-prop-×
  (Π-is-prop λ _ → W-set _ _)
  (is-prop-× (is-contr-is-prop _) (is-contr-is-prop _))

contractionᵂ : is-contr (Σ p ∶ pair tt , is-half-twist p)
contractionᵂ .center = half-twist-pair , half-twistᵂ
contractionᵂ .paths (p , T) =
  sym (Σ-prop-path is-half-twist-propᵂ (pins p (T .fst)))

framed-propᵂ : is-prop is-framed
framed-propᵂ = Π-is-prop λ x → is-contr→is-prop contractionᵂ

deductive-propᵂ : is-prop is-deductive-system-depreciated
deductive-propᵂ = deductive-prop framed-propᵂ
```

The cuts a recognition witness induces are the descriptor compositions
on the nose. Every witness induces the same edges, through the pinning
and the transport lemma. The mixed word whose junctions run positive
then negative still fails to associate over them.

```agda
module rec = recognized BW framedᵂ
module drv = rec.derived BW-embedding BW-comp⁺ BW-comp⁻

cut⁺-is-comp : (f g : W) → drv._⨾⁺_ f g ≡ comp f g
cut⁺-is-comp f g = refl

cut⁻-is-cut : (f g : W) → drv._⨾⁻_ f g ≡ cut⁻ f g
cut⁻-is-cut f g = refl

cut-canonical : (R : is-framed) (C : cuts R) (f g : W)
              → C .fst f g .center .fst ≡ comp f g
cut-canonical R C f g =
  transport-cuts.agree⁺ BW BW-embedding R framedᵂ
    (λ x → pins (R x .fst) (R x .snd .fst))
    (λ f' g' → C .fst f' g' .center)
    BW-comp⁺ f g

no-assoc : ¬ drv.associates τ̂ ε̂ ε̂
no-assoc = associates-refuted
```

## The cross-pair grammar

The canonical cross pair at the one ordered pair of objects is the
half-twist pair. Each gluing clause holds because an adjacent sandwich pins
its own pair first.

```agda
sandᵂ : sand tt tt (τ̂ , ε̂)
sandᵂ f = sandwich f

glueᵂ⁻ : glue⁻ tt tt (τ̂ , ε̂)
glueᵂ⁻ d Sd =
  subst (λ q → sand tt tt (τ̂ , q .snd)) (sym (pins d Sd)) sandᵂ

glueᵂ⁺ : glue⁺ tt tt (τ̂ , ε̂)
glueᵂ⁺ d Sd =
  subst (λ q → sand tt tt (q .fst , ε̂)) (sym (pins d Sd)) sandᵂ

predᵂ : pred tt tt (τ̂ , ε̂)
predᵂ = (sandᵂ , half-twists-inv) , glueᵂ⁻ , glueᵂ⁺
```

The mixed-pair argument against the canonical inhabitant returns the
same pinning that the sandwich alone gives.

```agda
playᵂ : (P Q : Σ c ∶ cross tt tt , pred tt tt c) → P .fst ≡ Q .fst
playᵂ P Q = play.pair-path P Q

recoverᵂ : (P : Σ c ∶ cross tt tt , pred tt tt c) → P .fst ≡ (τ̂ , ε̂)
recoverᵂ P = playᵂ P ((τ̂ , ε̂) , predᵂ)
```

The homs form a set, so every clause of the predicate is a proposition
and the pinning contracts the whole type.

```agda
sand-propᵂ : (c : cross tt tt) → is-prop (sand tt tt c)
sand-propᵂ c = Π-is-prop λ _ → W-set _ _

pred-propᵂ : (c : cross tt tt) → is-prop (pred tt tt c)
pred-propᵂ c = is-prop-×
  (is-prop-× (sand-propᵂ c)
    (is-prop-× (is-contr-is-prop _) (is-contr-is-prop _)))
  (is-prop-×
    (Πi-is-prop λ _ → Π-is-prop λ d → Π-is-prop λ _ →
      Π-is-prop λ _ → W-set _ _)
    (Πi-is-prop λ _ → Π-is-prop λ d → Π-is-prop λ _ →
      Π-is-prop λ _ → W-set _ _))

cross-contractionᵂ : is-contr (Σ c ∶ cross tt tt , pred tt tt c)
cross-contractionᵂ .center = (τ̂ , ε̂) , predᵂ
cross-contractionᵂ .paths (c , P) =
  sym (Σ-prop-path pred-propᵂ (pins c (P .fst .fst)))
```
