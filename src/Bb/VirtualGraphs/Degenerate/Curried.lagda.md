A curried presentation of the same two hands, over a ternary embedding
operator rather than a binary composition read against a
representability image. The carrier is a bare vertex-and-edge family
with a reflexive edge at each vertex; `emb` closes an edge between an
incoming string and an outgoing string in one operation, and each hand
reads that operation with the far slot pinned at the reflexive edge.

`yon` carries an edge into `x` forward along `f : edge x y`, pinning
`emb`'s outgoing slot at `rx y`. `noy` carries an edge out of `y`
backward along `f`, pinning the incoming slot at `rx x`. `ev` pins
both, which is `emb`'s reading of `f` alone. A composable pair `f , g`
spans two strings, one per hand: `E▿` fixes the incoming edge and
reads the outgoing slot through `g` pulled back along it; `E▵` reads
the incoming slot through `f` pushed forward along it and fixes the
outgoing edge. Each hand's composite is the center of the fiber of
`emb` over its own string — a fiber over a string, not over a shared
representability image, so the two compositions need not agree until
a further hypothesis says so.

This is a curried restatement of the `act-π`/`coact-π` vocabulary
`Bb.VirtualGraphs.Degenerate.Chosen` states directly over `reflect`; its results
are not re-derived here.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Curried where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)
```

```agda

module vgraph {v e} (vtx : Type v) (edge : vtx → vtx → Type e)
  (rx : (x : vtx) → edge x x)
  (emb : ∀ {x y} → edge x y → ∀ w → edge w x → ∀ z → edge y z → edge w z)
  where

  yon : ∀ {x y} → edge x y → ∀ w → edge w x → edge w y
  yon {y = y} f w a = emb f w a y (rx y)

  noy : ∀ {x y} → edge x y → ∀ z → edge y z → edge x z
  noy {x} f z b = emb f x (rx x) z b

  ev : ∀ {x y} → edge x y → edge x y
  ev {x} {y} f = emb f x (rx x) y (rx y)

  E▿ : ∀ {x y z} → edge x y → edge y z
     → ∀ w → edge w x → ∀ t → edge z t → edge w t
  E▿ f g w a t b = emb f w a t (noy g t b)

  E▵ : ∀ {x y z} → edge x y → edge y z
     → ∀ w → edge w x → ∀ t → edge z t → edge w t
  E▵ f g w a t b = emb g w (yon f w a) t b
```

## Composability: two conditions, two compositions

A composability hypothesis is stated per hand, one fiber of `emb` per
string. Nothing yet ties the two: each condition names its own
composite, and each composite distributes over its own hand's action,
read at the fiber center's own witness.

```agda

  module hands
    (pull-contr : ∀ {x y z} (f : edge x y) (g : edge y z)
                → is-contr (fiber (emb {x} {z}) (E▿ f g)))
    (push-contr : ∀ {x y z} (f : edge x y) (g : edge y z)
                → is-contr (fiber (emb {x} {z}) (E▵ f g)))
    where

    _⨾▿_ : ∀ {x y z} → edge x y → edge y z → edge x z
    f ⨾▿ g = pull-contr f g .center .fst
    infixr 40 _⨾▿_

    _⨾▵_ : ∀ {x y z} → edge x y → edge y z → edge x z
    f ⨾▵ g = push-contr f g .center .fst
    infixr 40 _⨾▵_

    noy-composite
      : ∀ {x y z} (f : edge x y) (g : edge y z) {t} (b : edge z t)
      → noy (f ⨾▿ g) t b ≡ noy f t (noy g t b)
    noy-composite {x} f g b i = pull-contr f g .center .snd i x (rx x) _ b

    yon-composite
      : ∀ {x y z} (f : edge x y) (g : edge y z) {w} (a : edge w x)
      → yon (f ⨾▵ g) w a ≡ yon g w (yon f w a)
    yon-composite {z = z} f g a i = push-contr f g .center .snd i _ a z (rx z)
```

## The unit tier: both compositions, idempotent at the reflexive edge

Both idempotences land on the reflexive edge, so the two compositions
agree there, and only there — this is the sole point the tier relates
them.

```agda

    module unital
      (pull-eqv : ∀ {x t} → is-equiv (noy (rx x) t))
      (push-eqv : ∀ {x w} → is-equiv (yon (rx x) w))
      (idem▿ : ∀ {x} → rx x ⨾▿ rx x ≡ rx x)
      (idem▵ : ∀ {x} → rx x ⨾▵ rx x ≡ rx x)
      where

      coincide : ∀ {x} → rx x ⨾▿ rx x ≡ rx x ⨾▵ rx x
      coincide = idem▿ ∙ sym idem▵
```

Each absorption is its own hand's cancellation: the unit action
against its own idempotence, over its own distributivity. Neither
hand's data enters the other's derivation.

```agda

      absorb▿ : ∀ {x t} (b : edge x t) → noy (rx x) t b ≡ b
      absorb▿ {x} {t} b = equiv→lc pull-eqv step
        where
        step : noy (rx x) t (noy (rx x) t b) ≡ noy (rx x) t b
        step = sym (noy-composite (rx x) (rx x) b)
             ∙ ap (λ s → noy s t b) idem▿

      absorb▵ : ∀ {x w} (a : edge w x) → yon (rx x) w a ≡ a
      absorb▵ {x} {w} a = equiv→lc push-eqv step
        where
        step : yon (rx x) w (yon (rx x) w a) ≡ yon (rx x) w a
        step = sym (yon-composite (rx x) (rx x) a)
             ∙ ap (λ s → yon s w a) idem▵
```

Each hand collapses its own string at the unit and inherits
contractibility from its own composability field, so the fiber over
`emb f` alone is available from either hand.

```agda

      shrink▿ : ∀ {x y} (f : edge x y) → E▿ f (rx y) ≡ emb f
      shrink▿ f i w a t b = emb f w a t (absorb▿ b i)

      emb-image-contr▿
        : ∀ {x y} (f : edge x y) → is-contr (fiber (emb {x} {y}) (emb f))
      emb-image-contr▿ {x} {y} f =
        subst (λ α → is-contr (fiber (emb {x} {y}) α))
              (shrink▿ f) (pull-contr f (rx y))

      shrink▵ : ∀ {x y} (f : edge x y) → E▵ (rx x) f ≡ emb f
      shrink▵ f i w a t b = emb f w (absorb▵ a i) t b

      emb-image-contr▵
        : ∀ {x y} (f : edge x y) → is-contr (fiber (emb {x} {y}) (emb f))
      emb-image-contr▵ {x} {y} f =
        subst (λ α → is-contr (fiber (emb {x} {y}) α))
              (shrink▵ f) (push-contr (rx x) f)
```

## The flanks

At the reflexive edge both slots of `emb` carry `rx`, so the two
absorptions above land in one shared type. Their agreement is
therefore a well-formed statement — `flank-pin` — but it is
uninhabited here: neither hand's own data supplies it.

```agda

      flank▿ : ∀ {x} → emb (rx x) x (rx x) x (rx x) ≡ rx x
      flank▿ {x} = absorb▿ (rx x)

      flank▵ : ∀ {x} → emb (rx x) x (rx x) x (rx x) ≡ rx x
      flank▵ {x} = absorb▵ (rx x)

      flank-pin : ∀ {x} → Type e
      flank-pin {x} = flank▿ {x} ≡ flank▵ {x}
```

## Stability is one statement, not two

Readback evaluates at the identity context, which fills both of
`emb`'s far slots at once, so the two hands' readback conditions
coincide in one equation rather than two. It delivers each hand's
unit law.

```agda

    module stable (readback : ∀ {x y} (f : edge x y) → ev f ≡ f) where

      comp-eq▿ : ∀ {x y z} (f : edge x y) (g : edge y z) → f ⨾▿ g ≡ noy f z g
      comp-eq▿ {z = z} f g =
          sym (readback (f ⨾▿ g))
        ∙ noy-composite f g (rx z)
        ∙ ap (noy f z) (readback g)

      comp-eq▵ : ∀ {x y z} (f : edge x y) (g : edge y z) → f ⨾▵ g ≡ yon g x f
      comp-eq▵ {x = x} f g =
          sym (readback (f ⨾▵ g))
        ∙ yon-composite f g (rx x)
        ∙ ap (yon g x) (readback f)

      unitr▿ : ∀ {x y} (f : edge x y) → f ⨾▿ rx y ≡ f
      unitr▿ {y = y} f = comp-eq▿ f (rx y) ∙ readback f

      unitl▵ : ∀ {x y} (f : edge x y) → rx x ⨾▵ f ≡ f
      unitl▵ {x} f = comp-eq▵ (rx x) f ∙ readback f
```
