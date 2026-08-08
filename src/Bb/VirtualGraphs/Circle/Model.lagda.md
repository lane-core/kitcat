The circle model: one object, homs the circle, both half-twist families
constant at `base`, reflection reading both flanks through the
multiplication. Reflection is an embedding even with wild homs — no
set condition enters — both cuts are contractibly representable on
the multiplication, and each absorption tier's fiber contracts at
`base`.

This module uses `--cubical`: it consumes `Circle-is-groupoid` in an
unerased position, which rides the winding equivalence `ua` builds.
The circle modules form their own import island; no `--erased-cubical`
module imports them unerased.

```agda
{-# OPTIONS --cubical --safe --no-guardedness --no-sized-types #-}

module Bb.VirtualGraphs.Circle.Model where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (J; subst)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (SinglP-contr; prop-inhabited→is-contr)
open import Core.Equiv.Base using (_≃_; iso→equiv)
open import Core.Equiv.Properties using (is-contr-equiv; Σ-equiv-snd)

open import HData.Circle
open Circle

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (is-representable; reflect-is-embedding)
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Absorb
```

## The carrier

Reflection sends an edge to the reader that multiplies it between
the two flanks. The fiber of reflection over a reflected edge is
contractible: currying is definitional, left translations cancel,
the first slot is faithful, and the path singleton remains. So the
embedding condition holds with no set condition on the homs.

```agda
module circle where

  rf : Circle → Sigma ⊤ (λ _ → Circle) × Sigma ⊤ (λ _ → Circle) → Circle
  rf m γ = mult (γ .fst .snd) (mult m (γ .snd .snd))

  model : virtual-graph 0ℓ 0ℓ
  model .virtual-graph.ob      = ⊤
  model .virtual-graph.hom _ _ = Circle
  model .virtual-graph.reflect = rf

  open framing model (λ _ → base) (λ _ → base)
  open absorbing⁻ model (λ _ → base)
  open absorbing⁺ model (λ _ → base)

  R : readback-of
  R f = mult-unit-r f

  private
    rev-path : {x y : Circle} → (x ≡ y) ≃ (y ≡ x)
    rev-path = iso→equiv (λ p i → p (~ i)) (λ p i → p (~ i))
      (λ _ → refl) (λ _ → refl)

    slice : (n m : Circle)
          → (rf n ≡ rf m)
          ≃ ((l r : Circle) → mult l (mult n r) ≡ mult l (mult m r))
    slice n m = iso→equiv
      (λ w l r i → w i ((tt , l) , (tt , r)))
      (λ v i γ → v (γ .fst .snd) (γ .snd .snd) i)
      (λ _ → refl) (λ _ → refl)

  rf-fiber-contr : (m : Circle) → is-contr (fiber rf (rf m))
  rf-fiber-contr m =
    is-contr-equiv (Σ-equiv-snd λ n → slice n m)
      (is-contr-equiv (Σ-equiv-snd λ n → mult-l-cancel)
        (is-contr-equiv (Σ-equiv-snd λ n → mult-faithful n m)
          (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
            (SinglP-contr {A = λ _ → Circle} m))))

  stable : reflect-is-embedding model
  stable α u v =
    is-contr→is-prop
      (subst (λ β → is-contr (fiber rf β)) (u .snd)
        (rf-fiber-contr (u .fst)))
      u v
```

## The cuts

Both cuts land on the multiplication. The positive cut is one
associativity whisker; the negative cut also crosses the right unit
law, because the coterm axiom sits inside `act`.

```agda
  C⁺ : is-composable⁺
  C⁺ f g = mult f g
         , λ i γ → mult (γ .fst .snd) (mult-assoc f g (γ .snd .snd) i)

  C⁻ : is-composable⁻
  C⁻ f g = mult f g
         , sym (funext λ γ →
             ap (λ t → mult (mult (γ .fst .snd) t) (mult g (γ .snd .snd)))
                (mult-unit-r f)
           ∙ (mult-assoc (γ .fst .snd) f (mult g (γ .snd .snd))
           ∙ ap (mult (γ .fst .snd)) (sym (mult-assoc f g (γ .snd .snd)))))

  cc⁺ : ∀ {x y z} (f g : Circle)
      → is-contr (is-representable model (composite⁺ {x} {y} {z} f g))
  cc⁺ f g = prop-inhabited→is-contr (stable _) (C⁺ f g)

  cc⁻ : ∀ {x y z} (f g : Circle)
      → is-contr (is-representable model (composite⁻ {x} {y} {z} f g))
  cc⁻ f g = prop-inhabited→is-contr (stable _) (C⁻ f g)
```

## The tiers

Each tier is the faithfulness of translation at the unit. The coterm
side is definitional; the term side crosses the right unit law
twice, once to evaluate the family and once to move the centre onto
`base`.

```agda
  private
    slice⁻ : (e : Circle)
           → (coact-π {tt} {tt} e ≡ snd) ≃ ((r : Circle) → mult e r ≡ r)
    slice⁻ e = iso→equiv
      (λ w r i → w i (tt , r))
      (λ v i γ → v (γ .snd) i)
      (λ _ → refl) (λ _ → refl)

    slice⁺ : (e : Circle)
           → (act-π {tt} {tt} e ≡ snd)
           ≃ ((l : Circle) → mult l (mult e base) ≡ l)
    slice⁺ e = iso→equiv
      (λ w l i → w i (tt , l))
      (λ v i t → v (t .snd) i)
      (λ _ → refl) (λ _ → refl)

    eval-free : (c : Circle) → ((l : Circle) → mult l c ≡ l) ≃ (c ≡ base)
    eval-free c = iso→equiv to fro sec retr
      where
      to : ((l : Circle) → mult l c ≡ l) → c ≡ base
      to w = w base

      fro : c ≡ base → (l : Circle) → mult l c ≡ l
      fro v l = ap (mult l) v ∙ mult-unit-r l

      sec : (w : (l : Circle) → mult l c ≡ l) → fro (to w) ≡ w
      sec w = funext (ind (λ l → fro (to w) l ≡ w l)
        (Path.unitr (w base))
        (is-prop→PathP (λ i → Circle-is-groupoid _ _ _ _)
          (Path.unitr (w base)) (Path.unitr (w base))))

      retr : (v : c ≡ base) → to (fro v) ≡ v
      retr v = Path.unitr v

    unit-conj : (e : Circle) → (mult e base ≡ base) ≃ (e ≡ base)
    unit-conj e = iso→equiv to fro sec retr
      where
      H : mult e base ≡ e
      H = mult-unit-r e

      to : mult e base ≡ base → e ≡ base
      to v = sym H ∙ v

      fro : e ≡ base → mult e base ≡ base
      fro u = H ∙ u

      sec : (v : mult e base ≡ base) → fro (to v) ≡ v
      sec v = Path.assoc H (sym H) v
            ∙ (ap (_∙ v) (Path.invr H) ∙ Path.unitl v)

      retr : (u : e ≡ base) → to (fro u) ≡ u
      retr u = Path.assoc (sym H) H u
             ∙ (ap (_∙ u) (Path.invl H) ∙ Path.unitl u)

  tier⁻ : is-contr (fiber (coact-π {tt} {tt}) snd)
  tier⁻ =
    is-contr-equiv (Σ-equiv-snd λ e → slice⁻ e)
      (is-contr-equiv (Σ-equiv-snd λ e → mult-faithful e base)
        (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
          (SinglP-contr {A = λ _ → Circle} base)))

  tier⁺ : is-contr (fiber (act-π {tt} {tt}) snd)
  tier⁺ =
    is-contr-equiv (Σ-equiv-snd λ e → slice⁺ e)
      (is-contr-equiv (Σ-equiv-snd λ e → eval-free (mult e base))
        (is-contr-equiv (Σ-equiv-snd λ e → unit-conj e)
          (is-contr-equiv (Σ-equiv-snd λ _ → rev-path)
            (SinglP-contr {A = λ _ → Circle} base))))

  T⁻ : is-absorbing⁻
  T⁻ _ = tier⁻

  T⁺ : is-absorbing⁺
  T⁺ _ = tier⁺
```
