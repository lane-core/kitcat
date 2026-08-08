The path groupoid on a type, framed by two arbitrary families of
loops. Representability is total, so every hypothesis group holds
with no condition on the framing and no h-level on the type: the
framing is free and the package is inhabited untruncated. What the
framing then decides is where the half-twists sit. Each hand's unit is
that hand's tier's own centre and exists at every framing; the
half-twists are the centres of the cell fibers instead, and whether the
two centres coincide is one equation — the composite of the half-twists
at an object is trivial. A neutral unit and a nontrivial framing are
not in competition: the neutral unit is simply not a half-twist. The
one-half-twist instance closes the file: at an arbitrary one-sided
framing the extraction telescope is inhabited entire. Where the
positive family is reflexivity, each cut has a closed value in the
path algebra, both naturality squares hold, and over a type whose
path spaces are sets both naturality tiers hold as well.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Groupoid.Path where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom; module Path; pcom→∙; is-contr→is-prop)
open import Core.Path.Base
open import Core.Homotopy using (homotopy-natural)
open import Core.HLevel.Base using (Π-is-hlevel)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (is-contr-×; prop-inhabited→is-contr)
open import Core.Equiv.Base
  using (_≃_; is-equiv; eqv-fibers; iso→equiv; is-contr-equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Naturality
open import Bb.VirtualGraphs.Degenerate.Tower
open import Bb.VirtualGraphs.Degenerate.Extraction
```

## The carrier

```agda
module path {u} {A : Type u} (t⁺ t⁻ : (x : A) → x ≡ x) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  PG : virtual-graph u u
  PG .virtual-graph.ob          = A
  PG .virtual-graph.hom x y     = x ≡ y
  PG .virtual-graph.reflect f γ =
    emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  open virtual-graph PG using (term; coterm; judgment)
  open framing PG t⁻ t⁺
  open absorbing⁻ PG t⁻
  open absorbing⁺ PG t⁺

  term-contr : ∀ x → is-contr (term x)
  term-contr x .center = x , refl
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (coterm y)
  coterm-contr y .center = y , refl
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  recentre : ∀ {ℓ} {T : Type ℓ} → is-contr T → T → is-contr T
  recentre c t .center = t
  recentre c t .paths s = sym (c .paths t) ∙ c .paths s

  curry≃ : ∀ {x y} → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z) ≃ judgment x y
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  reflect-equiv : ∀ {x y} → is-equiv (virtual-graph.reflect PG {x} {y})
  reflect-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  slot≃ : ∀ {x y}
        → judgment x y ≃ ((t : term x) (γ : coterm y) → t .fst ≡ γ .fst)
  slot≃ = iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                    (λ _ → refl) (λ _ → refl)

  slot-swap≃ : ∀ {x y}
             → judgment x y ≃ ((γ : coterm y) (t : term x) → t .fst ≡ γ .fst)
  slot-swap≃ = iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                         (λ _ → refl) (λ _ → refl)

  coact-π-equiv : ∀ x → is-equiv (coact-π {x} {x})
  coact-π-equiv x =
    ( (virtual-graph.reflect PG , reflect-equiv)
    ∙e slot≃
    ∙e Π-contr-dom (recentre (term-contr x) (var x)) ) .snd

  act-π-equiv : ∀ x → is-equiv (act-π {x} {x})
  act-π-equiv x =
    ( (virtual-graph.reflect PG , reflect-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (covar x)) ) .snd
```

## The package, at any framing

```agda
  PG-embedding : reflect-is-embedding PG
  PG-embedding α = is-contr→is-prop (eqv-fibers reflect-equiv α)

  PG-composable⁺ : is-composable⁺
  PG-composable⁺ f g = eqv-fibers reflect-equiv (composite⁺ f g) .center

  PG-composable⁻ : is-composable⁻
  PG-composable⁻ f g = eqv-fibers reflect-equiv (composite⁻ f g) .center

  PG-unital⁻ : is-absorbing⁻
  PG-unital⁻ x = eqv-fibers (coact-π-equiv x) snd

  PG-unital⁺ : is-absorbing⁺
  PG-unital⁺ x = eqv-fibers (act-π-equiv x) snd

  open tower PG t⁻ t⁺ PG-embedding PG-composable⁺ PG-composable⁻
    using (_⨾⁺_; _⨾⁻_; reflect-⨾⁺; reflect-⨾⁻; lc)
```

## The half-twists are the cells' centres

Each action map being an equivalence makes its fiber over the cell
contractible as well. Read at the axiom half of the argument,
membership of that fiber is the flank exchange, so `pcom.lr` places
each half-twist in the other hand's cell fiber, and the argument half
being contractible carries it everywhere. The framing is not
consulted.

```agda
  cell-fiber⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) (cell⁻ x))
  cell-fiber⁻ x = eqv-fibers (coact-π-equiv x) (cell⁻ x)

  cell-fiber⁺ : ∀ x → is-contr (fiber (act-π {x} {x}) (cell⁺ x))
  cell-fiber⁺ x = eqv-fibers (act-π-equiv x) (cell⁺ x)

  pin⁻-axiom : ∀ x → coact-π (t⁺ x) (x , refl) ≡ cell⁻ x (x , refl)
  pin⁻-axiom x = sym (pcom.lr (t⁻ x) (t⁺ x))

  pin⁺-axiom : ∀ x → act-π (t⁻ x) (x , refl) ≡ cell⁺ x (x , refl)
  pin⁺-axiom x = pcom.lr (t⁻ x) (t⁺ x)

  pin⁻ : ∀ x → coact-π (t⁺ x) ≡ cell⁻ x
  pin⁻ x = funext λ γ →
    subst (λ c → coact-π (t⁺ x) c ≡ cell⁻ x c)
          (coterm-contr x .paths γ) (pin⁻-axiom x)

  pin⁺ : ∀ x → act-π (t⁻ x) ≡ cell⁺ x
  pin⁺ x = funext λ t →
    subst (λ s → act-π (t⁻ x) s ≡ cell⁺ x s)
          (term-contr x .paths t) (pin⁺-axiom x)

  corx-centre : ∀ x → cell-fiber⁻ x .center .fst ≡ t⁺ x
  corx-centre x = ap fst (cell-fiber⁻ x .paths (t⁺ x , pin⁻ x))

  rx-centre : ∀ x → cell-fiber⁺ x .center .fst ≡ t⁻ x
  rx-centre x = ap fst (cell-fiber⁺ x .paths (t⁻ x , pin⁺ x))

  corx-unique : ∀ x (e : x ≡ x) → coact-π e ≡ cell⁻ x → t⁺ x ≡ e
  corx-unique x e w =
    sym (corx-centre x) ∙ ap fst (cell-fiber⁻ x .paths (e , w))

  rx-unique : ∀ x (e : x ≡ x) → act-π e ≡ cell⁺ x → t⁻ x ≡ e
  rx-unique x e w =
    sym (rx-centre x) ∙ ap fst (cell-fiber⁺ x .paths (e , w))
```

Terms and coterms here are based path spaces, so a clause quantified
over one is a family over a contractible domain and collapses to its
value at the centre. Each self-referential unit clause therefore
reduces to one equation: the ternary composite of the edge with
itself against the trivial flank is trivial.

```agda
  unit-clause⁺ : ∀ x (e : x ≡ x)
            → ((t : term x) → virtual-graph.reflect PG e (t , (x , e)) ≡ t .snd)
            ≃ (emb e x refl x e ≡ refl)
  unit-clause⁺ x e =
    Π-contr-dom
      {B = λ t → virtual-graph.reflect PG e (t , (x , e)) ≡ t .snd}
      (term-contr x)

  unit-clause⁻ : ∀ x (e : x ≡ x)
            → ((γ : coterm x) → virtual-graph.reflect PG e ((x , e) , γ) ≡ γ .snd)
            ≃ (emb e x e x refl ≡ refl)
  unit-clause⁻ x e =
    Π-contr-dom
      {B = λ γ → virtual-graph.reflect PG e ((x , e) , γ) ≡ γ .snd}
      (coterm-contr x)
```

## One equation

The two cancellation hypotheses are the same equation read on the
two hands: the composite of the half-twists at an object is trivial.
That is the framing's own content, and nothing above it decides it —
the tiers hold either way.

```agda
  cancels : Type u
  cancels = ∀ x → pcom.composite refl (t⁻ x) (t⁺ x) ≡ refl

  trivial⁻ : cancels → ∀ x → cell⁻ x ≡ snd
  trivial⁻ K x = funext λ γ →
    subst (λ c → cell⁻ x c ≡ c .snd) (coterm-contr x .paths γ) (K x)

  trivial⁺ : cancels → ∀ x → cell⁺ x ≡ snd
  trivial⁺ K x = funext λ t →
    subst (λ s → cell⁺ x s ≡ s .snd) (term-contr x .paths t)
          (sym (pcom.lr (t⁻ x) (t⁺ x)) ∙ K x)

  module cancelled (K : cancels) where
    open unital PG t⁻ t⁺ PG-embedding PG-composable⁺ PG-composable⁻
      pin⁻ pin⁺ (trivial⁻ K) (trivial⁺ K) public
```

Under it each hand gains its one unit law and the half-twists compose to
half-twists: `unitr⁺`, `unitl⁻`, `pair⁻` and `pair⁺` come from the
module, crossed as the tiers predict.

## A unit exists regardless

A right unit for the coterm hand is an edge whose action is the
second projection, which is what that hand's tier already asks for,
and representability being total makes the tier hold at every
framing. What the equation decides is only whether that unit is the
half-twist: the half-twist inhabits the `snd`-fiber precisely under `cancels`,
and contractibility identifies it with the neutral.

```agda
  neutral⁻ : ∀ x → fiber (coact-π {x} {x}) snd
  neutral⁻ x = PG-unital⁻ x .center

  neutral⁻-absorb : ∀ {y} (k : coterm y) → coact (neutral⁻ y .fst) k ≡ k
  neutral⁻-absorb {y} k i = k .fst , neutral⁻ y .snd i k

  neutral⁻-unitr : ∀ {x y} (f : x ≡ y) → f ⨾⁺ neutral⁻ y .fst ≡ f
  neutral⁻-unitr f = lc
    ( reflect-⨾⁺ f (neutral⁻ _ .fst)
    ∙ (λ i γ → virtual-graph.reflect PG f (γ .fst , neutral⁻-absorb (γ .snd) i)) )

  neutral⁺ : ∀ x → fiber (act-π {x} {x}) snd
  neutral⁺ x = PG-unital⁺ x .center

  neutral⁺-absorb : ∀ {x} (t : term x) → act (neutral⁺ x .fst) t ≡ t
  neutral⁺-absorb {x} t i = t .fst , neutral⁺ x .snd i t

  neutral⁺-unitl : ∀ {x y} (g : x ≡ y) → neutral⁺ x .fst ⨾⁻ g ≡ g
  neutral⁺-unitl g = lc
    ( reflect-⨾⁻ (neutral⁺ _ .fst) g
    ∙ (λ i γ → virtual-graph.reflect PG g (neutral⁺-absorb (γ .fst) i , γ .snd)) )

  module _ (K : cancels) where
    half-twist-is-neutral⁻ : ∀ x → neutral⁻ x .fst ≡ t⁺ x
    half-twist-is-neutral⁻ x =
      ap fst (PG-unital⁻ x .paths (t⁺ x , pin⁻ x ∙ trivial⁻ K x))

    half-twist-is-neutral⁺ : ∀ x → neutral⁺ x .fst ≡ t⁻ x
    half-twist-is-neutral⁺ x =
      ap fst (PG-unital⁺ x .paths (t⁻ x , pin⁺ x ∙ trivial⁺ K x))
```

## The one-half-twist instance

At an arbitrary one-sided framing over an arbitrary type, the
extraction telescope is inhabited entire, with no h-level
hypothesis: the carrier imposes no truncation.

```agda
module one-half-twist {u} {A : Type u} (t⁻ : (x : A) → x ≡ x) where

  open path t⁻ t⁻ using
    (PG; coact-π-equiv; reflect-equiv; slot-swap≃; coterm-contr; recentre)

  U⁻ : absorbing⁻.is-absorbing⁻ PG t⁻
  U⁻ x = eqv-fibers (coact-π-equiv x) snd

  open extraction PG t⁻ U⁻

  S : reflect-is-embedding PG
  S α = is-contr→is-prop (eqv-fibers reflect-equiv α)

  C⁺ : is-composable⁺
  C⁺ f g = eqv-fibers reflect-equiv (composite⁺ f g) .center

  C⁻ : is-composable⁻
  C⁻ f g = eqv-fibers reflect-equiv (composite⁻ f g) .center

  act-π-equiv : ∀ x → is-equiv (act-π {x} {x})
  act-π-equiv x =
    ( (virtual-graph.reflect PG , reflect-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (x , corx x)) ) .snd

  U⁺ : is-absorbing⁺
  U⁺ x = eqv-fibers (act-π-equiv x) snd

  open extraction.system⁻ PG t⁻ U⁻ S C⁺ C⁻ U⁺
    using (unitl⁻; cancel⁺; agree)
```

## Naturality at a reflexive positive family

Hold the positive family at reflexivity and leave the negative one an
arbitrary self-path family. Evaluation at the trivial argument
inverts reflection, so each cut has a closed value: the negative cut
is path composition, and the positive cut carries the remaining
family at its junction.

```agda
module naturality {u} {A : Type u} (θ : (x : A) → x ≡ x) where

  open path {A = A} (λ _ → refl) θ public
  open virtual-graph PG public using (ob; hom; judgment; reflect)
  open transfer PG θ (λ _ → refl) PG-embedding PG-composable⁺ PG-composable⁻ public
  open framing PG θ (λ _ → refl) public
    using (axiom; eval; readback-of; own⁻; own⁺;
           is-natural⁻; is-natural⁺; is-naturalᴶ⁻; is-naturalᴶ⁺)

  pt : ∀ {x y} → judgment x y → hom x y
  pt {x} {y} α = α ((x , refl) , (y , refl))

  pt-reflect : ∀ {x y} (f : hom x y) → pt (reflect f) ≡ f
  pt-reflect f = Path.unitr f

  cut⁻-value : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ∙ g
  cut⁻-value f g =
      sym (pt-reflect (f ⨾⁻ g))
    ∙ ap pt (reflect-⨾⁻ f g)
    ∙ pcom→∙ (f ∙ refl) g refl
    ∙ (λ i → Path.unitr f i ∙ Path.unitr g i)

  cut⁺-value : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁺ g ≡ f ∙ (θ y ∙ g)
  cut⁺-value {y = y} f g =
      sym (pt-reflect (f ⨾⁺ g))
    ∙ ap pt (reflect-⨾⁺ f g)
    ∙ ap (f ∙_) (pcom→∙ (θ y) g refl)
    ∙ ap (λ w → f ∙ (θ y ∙ w)) (Path.unitr g)
```

A self-path family commutes past every path, so both squares hold at
every such framing.

```agda
  nat-path : ∀ {x y} (m : hom x y) → θ x ∙ m ≡ m ∙ θ y
  nat-path m = sym (homotopy-natural {k = idfun A} {l = idfun A} θ m)

  square⁻ : nat⁻-law
  square⁻ {x} {y} m =
    cut⁻-value (θ x) m ∙ nat-path m ∙ sym (cut⁻-value m (θ y))

  square⁺ : nat⁺-law
  square⁺ {x} {y} m =
      cut⁺-value {x} {x} {y} refl m
    ∙ Path.unitl (θ x ∙ m)
    ∙ nat-path m
    ∙ sym (ap (m ∙_) (Path.unitr (θ y)))
    ∙ sym (cut⁺-value {x} {y} {y} m refl)
```

A judgment is a family of paths of the type, so path spaces of sets
make the judgments sets. Each tier then splits into a contractible
fiber, which reflection being an equivalence supplies, and a path
space of judgments, which is a proposition carrying the square.

```agda
  module tiers (gpd : (x y : A) → is-set (x ≡ y)) where

    jset : ∀ {x y} → is-set (judgment x y)
    jset = Π-is-hlevel 2 λ γ → gpd (γ .fst .fst) (γ .snd .fst)

    natural⁻ : is-natural⁻
    natural⁻ m =
      is-contr-equiv (centred≃ PG _ _)
        (is-contr-× (eqv-fibers reflect-equiv _)
                    (prop-inhabited→is-contr (jset _ _) (judg⁻ square⁻ m)))

    natural⁺ : is-natural⁺
    natural⁺ m =
      is-contr-equiv (centred≃ PG _ _)
        (is-contr-× (eqv-fibers reflect-equiv _)
                    (prop-inhabited→is-contr (jset _ _) (judg⁺ square⁺ m)))
```
