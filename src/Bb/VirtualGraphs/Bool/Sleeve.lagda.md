Two copies of the word model joined by a one-directional sleeve of
descriptors. The objects are the booleans. Both endo homs and the hom
from `true` to `false` are the canonical descriptors, and the reverse
direction is empty. Reflection is the word sandwich in every nonempty
case, so the word model's evaluation arithmetic covers the whole
carrier. The edges form sets, and evaluation of a reflection sandwiches
an edge between the two half-twists. So `reflect` is an embedding. Both cuts
are representable, by the word model's two compositions spread over the
object cases.

The per-object shape holds at the half-twist pair at each object. The
sandwich at a connecting edge reads the negative component at `true`
and the positive component at `false`, one from each endpoint.
`cross-reads` displays that reading definitionally. Each object pins
independently, so the framing type is a proposition as a product of two
contractions.

`coh` is the family readback at the connecting homs. With the diagonal
sandwiches it rebuilds the whole family readback, and the empty
direction contributes nothing. It is blind to the two components it
does not read, and it pins the two it does. Here the diagonal at both
objects gives it, so the amended record and the plain one convert.

The cross-pair grammar holds at the half-twist pair across the sleeve, and
its two gluing outputs pin the components `coh` leaves free. The
grammar's own predicate is empty at `(true , true)`. The empty
direction supplies vacuous sandwich instances, and the gluing clause
built from one of them demands a sandwich the word arithmetic refutes.
So the carrier has no cross-pair recognition.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Bool.Sleeve where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥; ¬_; ex-falso)
open import Core.Data.Nat
open import Core.Data.Bool
open import Core.HLevel.Base
  using (Π-is-prop; is-prop-×; Σ-prop-path; Π-is-hlevel)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Recognition
open import Bb.VirtualGraphs.Degenerate.Shape
open import Bb.VirtualGraphs.Degenerate.Gluing
open import Bb.VirtualGraphs.Word.Carrier
open import Bb.VirtualGraphs.Word.Model
open import Bb.VirtualGraphs.Word.Census
  using (frame-at; pair-path; ω̂; module recognize)
```

## The carrier

Two objects and three nonempty homs. Reflection goes by cases on the
four objects, because the hom family computes by cases.

```agda
edge : Bool → Bool → Type
edge true  true  = W
edge true  false = W
edge false true  = ⊥
edge false false = W

edge-set : (x y : Bool) → is-set (edge x y)
edge-set true  true      = W-set
edge-set true  false     = W-set
edge-set false true  a b = ex-falso a
edge-set false false     = W-set

rf : (x y : Bool) → edge x y → (w v : Bool)
   → edge w x → edge y v → edge w v
rf true  true  f true  true  a b = comp (comp (φW a) f) b
rf true  true  f true  false a b = comp (comp (φW a) f) b
rf true  true  f false v     a b = ex-falso a
rf true  false f true  true  a b = ex-falso b
rf true  false f true  false a b = comp (comp (φW a) f) b
rf true  false f false v     a b = ex-falso a
rf false true  f w     v     a b = ex-falso f
rf false false f true  true  a b = ex-falso b
rf false false f true  false a b = comp (comp (φW a) f) b
rf false false f false true  a b = ex-falso b
rf false false f false false a b = comp (comp (φW a) f) b

neg pos : (x : Bool) → edge x x
neg true  = τ̂
neg false = τ̂
pos true  = ε̂
pos false = ε̂

EC : virtual-graph 0ℓ 0ℓ
EC .virtual-graph.ob = Bool
EC .virtual-graph.hom = edge
EC .virtual-graph.reflect {x} {y} f γ =
  rf x y f (γ .fst .fst) (γ .snd .fst) (γ .fst .snd) (γ .snd .snd)

open virtual-graph EC using (hom; term; coterm; reflect)
open framing EC neg pos
  using ( eval; embedding-from-hom-sets; composite⁺; composite⁻ )

no-return : ¬ hom false true
no-return e = e
```

## The embedding condition

Evaluation of a reflection sandwiches the edge between the two half-twists
in every nonempty case. So the word model's sandwich collapse makes
transmission injective. The homs are sets, so `reflect` is an embedding
everywhere.

```agda
inj : (x y : Bool) {m n : edge x y}
    → eval (reflect m) ≡ eval (reflect n) → m ≡ n
inj true  true  {m} {n} p = sym (sandwich m) ∙ p ∙ sandwich n
inj true  false {m} {n} p = sym (sandwich m) ∙ p ∙ sandwich n
inj false true  {m}     p = ex-falso m
inj false false {m} {n} p = sym (sandwich m) ∙ p ∙ sandwich n

stableᴱ : reflect-is-embedding EC
stableᴱ = embedding-from-hom-sets (λ {x} {y} → edge-set x y)
                                  (λ {x} {y} → inj x y)
```

## Both cuts are representable

The candidate representatives are the word model's two compositions,
spread over the object cases. Each pointwise equation is the word
model's own cut path, unchanged. Reflection at literal objects computes
to the word formula.

```agda
cp : (x y z : Bool) → edge x y → edge y z → edge x z
cp true  true  true  f g = comp f g
cp true  true  false f g = comp f g
cp true  false true  f g = ex-falso g
cp true  false false f g = comp f g
cp false true  z     f g = ex-falso f
cp false false true  f g = ex-falso g
cp false false false f g = comp f g

cm : (x y z : Bool) → edge x y → edge y z → edge x z
cm true  true  true  f g = cut⁻ f g
cm true  true  false f g = cut⁻ f g
cm true  false true  f g = ex-falso g
cm true  false false f g = cut⁻ f g
cm false true  z     f g = ex-falso f
cm false false true  f g = ex-falso g
cm false false false f g = cut⁻ f g

eq⁺ : (x y z w v : Bool) (f : edge x y) (g : edge y z)
      (a : edge w x) (b : edge z v)
    → rf x z (cp x y z f g) w v a b
    ≡ composite⁺ f g ((w , a) , (v , b))
eq⁺ true true true true true f g a b =
  ev-inj _ _ (cut⁺-path a f g b)
eq⁺ true true true true false f g a b =
  ev-inj _ _ (cut⁺-path a f g b)
eq⁺ true true true false v f g a b = ex-falso a
eq⁺ true true false true true f g a b = ex-falso b
eq⁺ true true false true false f g a b =
  ev-inj _ _ (cut⁺-path a f g b)
eq⁺ true true false false v f g a b = ex-falso a
eq⁺ true false true w v f g a b = ex-falso g
eq⁺ true false false true true f g a b = ex-falso b
eq⁺ true false false true false f g a b =
  ev-inj _ _ (cut⁺-path a f g b)
eq⁺ true false false false v f g a b = ex-falso a
eq⁺ false true z w v f g a b = ex-falso f
eq⁺ false false true w v f g a b = ex-falso g
eq⁺ false false false true true f g a b = ex-falso b
eq⁺ false false false true false f g a b =
  ev-inj _ _ (cut⁺-path a f g b)
eq⁺ false false false false true f g a b = ex-falso b
eq⁺ false false false false false f g a b =
  ev-inj _ _ (cut⁺-path a f g b)

eq⁻ : (x y z w v : Bool) (f : edge x y) (g : edge y z)
      (a : edge w x) (b : edge z v)
    → rf x z (cm x y z f g) w v a b
    ≡ composite⁻ f g ((w , a) , (v , b))
eq⁻ true true true true true f g a b =
  ev-inj _ _ (cut⁻-path a f g b)
eq⁻ true true true true false f g a b =
  ev-inj _ _ (cut⁻-path a f g b)
eq⁻ true true true false v f g a b = ex-falso a
eq⁻ true true false true true f g a b = ex-falso b
eq⁻ true true false true false f g a b =
  ev-inj _ _ (cut⁻-path a f g b)
eq⁻ true true false false v f g a b = ex-falso a
eq⁻ true false true w v f g a b = ex-falso g
eq⁻ true false false true true f g a b = ex-falso b
eq⁻ true false false true false f g a b =
  ev-inj _ _ (cut⁻-path a f g b)
eq⁻ true false false false v f g a b = ex-falso a
eq⁻ false true z w v f g a b = ex-falso f
eq⁻ false false true w v f g a b = ex-falso g
eq⁻ false false false true true f g a b = ex-falso b
eq⁻ false false false true false f g a b =
  ev-inj _ _ (cut⁻-path a f g b)
eq⁻ false false false false true f g a b = ex-falso b
eq⁻ false false false false false f g a b =
  ev-inj _ _ (cut⁻-path a f g b)

rep⁺ : (x y z : Bool) (f : edge x y) (g : edge y z)
     → reflect {x} {z} (cp x y z f g) ≡ composite⁺ f g
rep⁺ x y z f g = funext λ γ →
  eq⁺ x y z (γ .fst .fst) (γ .snd .fst) f g (γ .fst .snd) (γ .snd .snd)

rep⁻ : (x y z : Bool) (f : edge x y) (g : edge y z)
     → reflect {x} {z} (cm x y z f g) ≡ composite⁻ f g
rep⁻ x y z f g = funext λ γ →
  eq⁻ x y z (γ .fst .fst) (γ .snd .fst) f g (γ .fst .snd) (γ .snd .snd)

composable⁺ : framing⁻.is-composable⁺ EC neg
composable⁺ {x} {y} {z} f g = cp x y z f g , rep⁺ x y z f g

composable⁻ : framing⁺.is-composable⁻ EC pos
composable⁻ {x} {y} {z} f g = cm x y z f g , rep⁻ x y z f g
```

## The per-object shape

The canonical family puts the half-twist pair at each object. The sandwich
clause is the collapse per object. Each invertibility fiber contracts
at its own half-twist, with the quantifiers spread over the two-object terms
and coterms.

```agda
open shape EC
  using ( pair; flanks; is-half-twist; is-framed; family; rbᶠ; frame-of
        ; coact-πᵗ; act-πᵗ; inv⁻ᵗ; inv⁺ᵗ; cuts; is-deductive-system-depreciated
        ; deductive-prop )

canonical : family
canonical x = neg x , pos x

flanksᴱ : (x : Bool) → flanks {x} (canonical x)
flanksᴱ true  f = sandwich f
flanksᴱ false f = sandwich f

coterm-set : (x : Bool) → is-set ((γ : coterm x) → edge x (γ .fst))
coterm-set x = Π-is-hlevel (S (S Z)) λ γ → edge-set x (γ .fst)

term-set : (x : Bool) → is-set ((t : term x) → edge (t .fst) x)
term-set x = Π-is-hlevel (S (S Z)) λ t → edge-set (t .fst) x

cε-t : (v : Bool) (c : edge true v) → rf true true ε̂ true v τ̂ c ≡ c
cε-t true  c = comp-unitl c
cε-t false c = comp-unitl c

cε-f : (v : Bool) (c : edge false v) → rf false false ε̂ false v τ̂ c ≡ c
cε-f true  c = ex-falso c
cε-f false c = comp-unitl c

coactε-t : coact-πᵗ {true} (canonical true) ε̂ ≡ snd
coactε-t = funext λ γ → cε-t (γ .fst) (γ .snd)

coactε-f : coact-πᵗ {false} (canonical false) ε̂ ≡ snd
coactε-f = funext λ γ → cε-f (γ .fst) (γ .snd)

q⁻-t : (e : W) → coact-πᵗ {true} (canonical true) e ≡ snd → ε̂ ≡ e
q⁻-t e pe = sym (sym (sandwich e) ∙ happly pe (true , ε̂))

q⁻-f : (e : W) → coact-πᵗ {false} (canonical false) e ≡ snd → ε̂ ≡ e
q⁻-f e pe = sym (sym (sandwich e) ∙ happly pe (false , ε̂))

aτ-t : (w : Bool) (a : edge w true) → rf true true τ̂ w true a ε̂ ≡ a
aτ-t true  a = act-τ a
aτ-t false a = ex-falso a

aτ-f : (w : Bool) (a : edge w false) → rf false false τ̂ w false a ε̂ ≡ a
aτ-f true  a = act-τ a
aτ-f false a = act-τ a

actτ-t : act-πᵗ {true} (canonical true) τ̂ ≡ snd
actτ-t = funext λ t → aτ-t (t .fst) (t .snd)

actτ-f : act-πᵗ {false} (canonical false) τ̂ ≡ snd
actτ-f = funext λ t → aτ-f (t .fst) (t .snd)

q⁺-t : (e : W) → act-πᵗ {true} (canonical true) e ≡ snd → τ̂ ≡ e
q⁺-t e pe = sym (sym (sandwich e) ∙ happly pe (true , τ̂))

q⁺-f : (e : W) → act-πᵗ {false} (canonical false) e ≡ snd → τ̂ ≡ e
q⁺-f e pe = sym (sym (sandwich e) ∙ happly pe (false , τ̂))

inv⁻-t : inv⁻ᵗ {true} (canonical true)
inv⁻-t .center = ε̂ , coactε-t
inv⁻-t .paths (e , pe) i =
  q⁻-t e pe i
  , is-prop→PathP
      (λ j → coterm-set true
               (coact-πᵗ {true} (canonical true) (q⁻-t e pe j)) snd)
      coactε-t pe i

inv⁻-f : inv⁻ᵗ {false} (canonical false)
inv⁻-f .center = ε̂ , coactε-f
inv⁻-f .paths (e , pe) i =
  q⁻-f e pe i
  , is-prop→PathP
      (λ j → coterm-set false
               (coact-πᵗ {false} (canonical false) (q⁻-f e pe j)) snd)
      coactε-f pe i

inv⁺-t : inv⁺ᵗ {true} (canonical true)
inv⁺-t .center = τ̂ , actτ-t
inv⁺-t .paths (e , pe) i =
  q⁺-t e pe i
  , is-prop→PathP
      (λ j → term-set true
               (act-πᵗ {true} (canonical true) (q⁺-t e pe j)) snd)
      actτ-t pe i

inv⁺-f : inv⁺ᵗ {false} (canonical false)
inv⁺-f .center = τ̂ , actτ-f
inv⁺-f .paths (e , pe) i =
  q⁺-f e pe i
  , is-prop→PathP
      (λ j → term-set false
               (act-πᵗ {false} (canonical false) (q⁺-f e pe j)) snd)
      actτ-f pe i

half-twistᴱ : (x : Bool) → is-half-twist {x} (canonical x)
half-twistᴱ true  = flanksᴱ true  , inv⁻-t , inv⁺-t
half-twistᴱ false = flanksᴱ false , inv⁻-f , inv⁺-f

framedᴱ : is-framed
framedᴱ x = canonical x , half-twistᴱ x

cutsᴱ : cuts framedᴱ
cutsᴱ =
    (λ f g → contr-from-embedding EC stableᴱ _ (composable⁺ f g))
  , (λ f g → contr-from-embedding EC stableᴱ _ (composable⁻ f g))

deductiveᴱ : is-deductive-system-depreciated
deductiveᴱ = stableᴱ , framedᴱ , cutsᴱ
```

The sandwich at a connecting edge reads the negative component at
`true` and the positive component at `false`, one from each endpoint,
and nothing else. The display is definitional.

```agda
cross-reads : (P : family) (f : hom true false)
  → reflect {true} {false} f
      ((true , P true .fst) , (false , P false .snd))
  ≡ comp (comp (φW (P true .fst)) f) (P false .snd)
cross-reads P f = refl
```

## Each object pins independently

Per object the sandwich clause is the word model's recognition
equation. So the pinning returns the half-twist pair at each object
separately. Each recognition type contracts, and the framing type is a
proposition as a product of two independent contractions.

```agda
to-rb : (a b : W) → ((f : W) → comp (comp (φW a) f) b ≡ f)
      → candidate.rb BW (frame-at a b)
to-rb a b F f = F f

pins : (x : Bool) (p : pair x) → flanks {x} p → p ≡ canonical x
pins true  p F =
  pair-path (frame-at (p .fst) (p .snd))
    (to-rb (p .fst) (p .snd) F)
pins false p F =
  pair-path (frame-at (p .fst) (p .snd))
    (to-rb (p .fst) (p .snd) F)

half-twist-prop : (x : Bool) (p : pair x) → is-prop (is-half-twist {x} p)
half-twist-prop x p = is-prop-×
  (Π-is-prop λ f → edge-set x x _ _)
  (is-prop-× (is-contr-is-prop _) (is-contr-is-prop _))

contraction : (x : Bool) → is-contr (Σ p ∶ pair x , is-half-twist {x} p)
contraction x .center = canonical x , half-twistᴱ x
contraction x .paths (p , T) =
  sym (Σ-prop-path (half-twist-prop x) (pins x p (T .fst)))

framed-prop : is-prop is-framed
framed-prop = Π-is-prop λ x → is-contr→is-prop (contraction x)

system-prop : is-prop is-deductive-system-depreciated
system-prop = deductive-prop framed-prop
```

## The off-diagonal residue

`coh` is the family readback at the connecting homs. With the diagonal
sandwiches it rebuilds the whole family readback, and the empty
direction contributes nothing.

```agda
coh : family → Type
coh P = (f : hom true false)
      → reflect {true} {false} f
          ((true , P true .fst) , (false , P false .snd))
      ≡ f

residue : (P : family) → ((x : Bool) → flanks {x} (P x)) → coh P
        → (x y : Bool) (f : edge x y)
        → reflect {x} {y} f ((x , P x .fst) , (y , P y .snd)) ≡ f
residue P D C true  true  f = D true f
residue P D C true  false f = C f
residue P D C false true  f = ex-falso f
residue P D C false false f = D false f

rb-residue : (P : family) → ((x : Bool) → flanks {x} (P x)) → coh P
           → rbᶠ P
rb-residue P D C {x} {y} f = residue P D C x y f

rb-coh : (P : family) → rbᶠ P → coh P
rb-coh P R f = R {true} {false} f

cohᴱ : coh canonical
cohᴱ f = sandwich f
```

## What the residue reads

`coh` reads two of the four components. They are the negative one at
`true` and the positive one at `false`. The `blind` families fix those
two at the half-twists and leave the other two free. So `coh` holds at every
one of them, while the diagonal sandwich at `false` fails. The pair
`(τ̂ , τ̂)` fails both.

```agda
blind : W → W → family
blind c d true  = τ̂ , d
blind c d false = c , ε̂

coh-blind : (c d : W) → coh (blind c d)
coh-blind c d f = sandwich f

no-flanks-ω : ¬ flanks {false} (ω̂ , ε̂)
no-flanks-ω F = subst w-nil (sym (F ε̂)) tt

no-flanks-ε : ¬ flanks {false} (ε̂ , ε̂)
no-flanks-ε F = subst w-nil (sym (F ε̂)) tt

no-flanks-δ : ¬ flanks {false} (δ̂ , ε̂)
no-flanks-δ F = subst w-nil (sym (F ε̂)) tt

Pττ : family
Pττ true  = canonical true
Pττ false = τ̂ , τ̂

no-coh-ττ : ¬ coh Pττ
no-coh-ττ C = half-twist-distinct (C ε̂)

no-flanks-ττ : ¬ flanks {false} (τ̂ , τ̂)
no-flanks-ττ F = half-twist-distinct (F ε̂)
```

What `coh` reads, it pins outright. The condition at the connecting
homs is the word model's recognition equation for the pair of read
components.

```agda
coh-pins : (P : family) → coh P
         → (P true .fst ≡ τ̂) × (P false .snd ≡ ε̂)
coh-pins P C = recognize.pin-a p R , recognize.pin-b p R
  where
    p : candidate.frame BW
    p = frame-at (P true .fst) (P false .snd)

    R : candidate.rb BW p
    R f = C f
```

A family with the diagonal sandwich at both objects pins per object,
and the transported sandwich closes `coh`.

```agda
diag→coh : (P : family) → ((x : Bool) → flanks {x} (P x)) → coh P
diag→coh P D f =
  (λ i → reflect {true} {false} f
     ((true , pins true (P true) (D true) i .fst)
    , (false , pins false (P false) (D false) i .snd)))
  ∙ sandwich f
```

## Two coherent families

The two coherences force the components they read to agree, one at each
object. The far components stay free.

```agda
play-pins : (P Q : family) → coh P → coh Q
          → (P true .fst ≡ Q true .fst) × (P false .snd ≡ Q false .snd)
play-pins P Q CP CQ =
    coh-pins P CP .fst ∙ sym (coh-pins Q CQ .fst)
  , coh-pins P CP .snd ∙ sym (coh-pins Q CQ .snd)

snd-free : ¬ ((P Q : family) → coh P → coh Q
             → P true .snd ≡ Q true .snd)
snd-free H =
  subst w-nil
    (H (blind ε̂ ε̂) (blind ε̂ δ̂) (coh-blind ε̂ ε̂) (coh-blind ε̂ δ̂)) tt

fst-free : ¬ ((P Q : family) → coh P → coh Q
             → P false .fst ≡ Q false .fst)
fst-free H =
  subst w-nil
    (H (blind ε̂ ε̂) (blind δ̂ ε̂) (coh-blind ε̂ ε̂) (coh-blind δ̂ ε̂)) tt
```

## The edge-indexed conjunct

The diagonal pins here, so the conjunct follows from the record it
extends and the two records convert.

```agda
complete : is-deductive-system-depreciated → coherence.is-coherent-deductive-system-depreciated EC
complete (E , R , C) =
  E , R , C
  , rb-residue (frame-of R) (λ x → R x .snd .fst)
      (diag→coh (frame-of R) (λ x → R x .snd .fst))

strip : coherence.is-coherent-deductive-system-depreciated EC → is-deductive-system-depreciated
strip (E , R , C , _) = E , R , C
```

## The cross-pair grammar across the sleeve

The canonical cross pair at every ordered pair of objects is the half-twist
pair, and each nonempty sandwich is the word sandwich. Both gluing
forms with the connecting instance as centre land on word sandwiches.
The adjacent sandwich pins its own pair first.

```agda
open grammar EC using (cross; sand; glue⁻; glue⁺; pred; recognized)

sand-tt : sand true true (τ̂ , ε̂)
sand-tt f = sandwich f

sand-ff : sand false false (τ̂ , ε̂)
sand-ff f = sandwich f

sand-tf : sand true false (τ̂ , ε̂)
sand-tf f = sandwich f

glue-sleeveˡ : (d : cross true true) → sand true true d
             → sand true true (τ̂ , d .snd)
glue-sleeveˡ d Sd =
  subst (λ b → sand true true (τ̂ , b))
    (sym (recognize.pin-b (frame-at (d .fst) (d .snd))
                          (to-rb (d .fst) (d .snd) Sd)))
    sand-tt

glue-sleeveʳ : (d : cross false false) → sand false false d
             → sand false false (d .fst , ε̂)
glue-sleeveʳ d Sd =
  subst (λ a → sand false false (a , ε̂))
    (sym (recognize.pin-a (frame-at (d .fst) (d .snd))
                          (to-rb (d .fst) (d .snd) Sd)))
    sand-ff
```

The gluing outputs pin the two components `coh` is blind to.

```agda
out-pins-d : (d : W) → sand true true (τ̂ , d) → d ≡ ε̂
out-pins-d d Sd = recognize.pin-b (frame-at τ̂ d) (to-rb τ̂ d Sd)

out-pins-c : (c : W) → sand false false (c , ε̂) → c ≡ τ̂
out-pins-c c Sc = recognize.pin-a (frame-at c ε̂) (to-rb c ε̂ Sc)

no-out-ττ : ¬ sand true true (τ̂ , τ̂)
no-out-ττ Sd = half-twist-distinct (out-pins-d τ̂ Sd)
```

The hom from `false` to `true` is empty, so every cross pair over it
carries the sandwich vacuously. A gluing clause at `(true , true)` then
returns a sandwich whose second component is the negative half-twist. The
word arithmetic refutes that sandwich. So the predicate is empty at
`(true , true)`, and the carrier carries no cross-pair recognition.

```agda
no-sand-uτ : (u : W) → ¬ sand true true (u , τ̂)
no-sand-uτ u R =
  half-twist-distinct (recognize.pin-b (frame-at u τ̂) (to-rb u τ̂ R))

no-pred-ttᴱ : (c : cross true true) → ¬ pred true true c
no-pred-ttᴱ c P =
  no-sand-uτ (c .fst)
    (P .snd .fst {false} (τ̂ , τ̂) (λ e → ex-falso e))

no-recognizedᴱ : ¬ recognized
no-recognizedᴱ R = no-pred-ttᴱ (R true true .fst) (R true true .snd)
```
