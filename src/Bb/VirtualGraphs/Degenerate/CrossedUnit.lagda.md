The chosen family enters the coterm hand's projection, `coact-π`, in its
term slot and nowhere else. That projection's own unit fiber produces a
filler edge, `unit⁻`, and the derived coterm `covar⁻` built from it. The
term hand's action, `act-π⁻`, reads through that filler rather than
through the chosen family a second time, so its own unit tier —
`is-unital⁺`, a fiber of `act-π⁻` — never mentions the chosen family at
all. The exchange hypothesis names the one step the coterm hand's
composability does not already supply on its own, and with it the
chosen family absorbs under `act-π⁻` directly.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.CrossedUnit where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (is-representable)
open import Bb.VirtualGraphs.Degenerate.Chosen
```

## The coterm hand's filler

Given the coterm hand's unit fiber, its centre is an edge, and that
edge fills the coterm slot the term hand's own action reads.

```agda
module crossed {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn using (coact-π; argue)

  module filler (U⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd)) where

    unit⁻ : (x : ob) → hom x x
    unit⁻ x = U⁻ x .center .fst

    covar⁻ : (y : ob) → coterm y
    covar⁻ y = y , unit⁻ y

    act-π⁻ : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
    act-π⁻ {y = y} f t = reflect f (argue t (covar⁻ y))
```

## The crossed unit tier

The filler, not the chosen family, is what `act-π⁻`'s own unit fiber is
stated against. Its centre and uniqueness clause read exactly as the
ordinary term-hand tier does, one projection later.

```agda
    is-unital⁺ : Type (o ⊔ h)
    is-unital⁺ = ∀ x → is-contr (fiber (act-π⁻ {x} {x}) snd)

    module _ (U⁺ : is-unital⁺) where

      unit⁺ : (x : ob) → hom x x
      unit⁺ x = U⁺ x .center .fst

      unit⁺-unique : ∀ x (e : hom x x) → act-π⁻ e ≡ snd → e ≡ unit⁺ x
      unit⁺-unique x e w = sym (ap fst (U⁺ x .paths (e , w)))
```

## The exchange

The coterm hand's composability, read at the chosen family and at the
filler in turn, collapses the composite of an edge with the filler to
that edge alone — but composability only says the composite is
represented, not that the chosen family's own `act-π⁻`-image represents
it. Naming that identification directly is the exchange hypothesis, and
from it the chosen family absorbs under `act-π⁻` with no further
condition.

```agda
module exchange {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn using (argue; coact; coact-π; composite⁻; composite⁺)

  module _
    (U⁻ : ∀ x → is-contr (fiber (coact-π {x} {x}) snd))
    (contr⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁻ f g)))
    (contr⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
            → is-contr (is-representable G (composite⁺ f g)))
    where

    open crossed.filler G idn U⁻ using (unit⁻; act-π⁻)
    open chosen.composable G idn contr⁻ contr⁺
```

The centre's defining path is a statement about the coterm slot alone,
so it lifts to the coterm transport and rewrites the composite judgment
back to its head — the same route the coterm hand's own right unit law
takes, restricted to the filler `unit⁻` rather than any assumed unit of
the whole carrier.

```agda
    private
      absorb-coact : ∀ {y} (γ : coterm y) → coact (unit⁻ y) γ ≡ γ
      absorb-coact {y} γ i = γ .fst , U⁻ y .center .snd i γ

      composite⁻-unitr
        : ∀ {x y} (f : hom x y) → composite⁻ f (unit⁻ y) ≡ reflect f
      composite⁻-unitr f i γ = reflect f (γ .fst , absorb-coact (γ .snd) i)

      reflect-image-contr
        : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
      reflect-image-contr {y = y} f =
        subst (λ α → is-contr (is-representable G α))
              (composite⁻-unitr f) (contr⁻ f (unit⁻ y))

      reflect-lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
      reflect-lc {n = n} p =
        sym (ap fst (reflect-image-contr n .paths (_ , p)))
        ∙ ap fst (reflect-image-contr n .paths (n , refl))

      ⨾⁻-unitr : ∀ {x y} (f : hom x y) → f ⨾⁻ unit⁻ y ≡ f
      ⨾⁻-unitr f = reflect-lc (reflect-⨾⁻ f (unit⁻ _) ∙ composite⁻-unitr f)
```

```agda
    exchange-hypothesis : Type (o ⊔ h)
    exchange-hypothesis =
      ∀ {w x} (u : hom w x)
      → reflect (act-π⁻ (idn x) (w , u)) ≡ composite⁻ u (unit⁻ x)

    module _ (E : exchange-hypothesis) where
      chosen-absorbs⁺-from-exchange
        : ∀ x (t : term x) → act-π⁻ (idn x) t ≡ t .snd
      chosen-absorbs⁺-from-exchange x t =
        reflect-lc (E (t .snd) ∙ sym (reflect-⨾⁻ (t .snd) (unit⁻ x)))
        ∙ ⨾⁻-unitr (t .snd)
```
