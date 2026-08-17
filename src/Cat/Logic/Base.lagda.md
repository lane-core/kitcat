```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path; is-contr→is-prop)
open import Core.Path.Base using (ap-comp)
open import Core.Transport.Properties
  using (is-prop→is-set; is-prop-is-prop; is-contr-is-prop; prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; is-prop-equiv; Π-is-hlevel)
open import Core.Function.Embedding
  using (is-embedding; injective→is-embedding; image-fibers-contr→is-embedding)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (is-equiv; iso→equiv)
open import Core.Equiv.Properties using (is-contr-equiv)

open import Cat.Logic.Type
```

Straightforward to define an opposite operation, and it's strictly involutive.

```agda
opⱽ : ∀ {o h} → virtual-graph o h → virtual-graph o h
opⱽ G .virtual-graph.ob        = virtual-graph.ob G
opⱽ G .virtual-graph.hom x y   = virtual-graph.hom G y x
opⱽ G .virtual-graph.reflect f γ = virtual-graph.reflect G f (γ .snd , γ .fst)

private
  opⱽ-invol : ∀ {o h} (G : virtual-graph o h) → opⱽ (opⱽ G) ≡ G
  opⱽ-invol G = refl
```

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G
  open sequents G

  argue : ∀ {x y} → term x → coterm y → argument x y
  argue h k = h , k

  intro : ∀ {x y} → hom x y → term y
  intro {x} f = x , f

  elim : ∀ {x y} → hom x y → coterm x
  elim {y = y} f = y , f

  assert : ∀ {w x y} → hom w x → (φ : coterm y) → argument x y
  assert {w} f φ .fst .fst = w
  assert f φ .fst .snd = f
  assert f φ .snd = φ

  is-left-neutral : ∀ {x y} → hom x y → term x → Type (o ⊔ h)
  is-left-neutral {x} {y} f p =
    ∀ {v} → is-equiv (λ (c : hom y v) → reflect f (p , elim c))

  is-right-neutral : ∀ {x y} → hom x y → coterm y → Type (o ⊔ h)
  is-right-neutral {x} {y} f c =
    ∀ {w} → is-equiv (λ (p : hom w x) → reflect f (intro p , c))

  is-unital : ob → Type (o ⊔ h)
  is-unital x =
    Σ i ∶ hom x x , is-left-neutral i (x , i)
                  × is-right-neutral i (x , i)
                  × (reflect i ((x , i) , (x , i)) ≡ i)

  is-stable : Type (o ⊔ h)
  is-stable = ∀ {x y} (α : judgment x y) → is-prop (is-representable α)

  is-stable-is-prop : is-prop is-stable
  is-stable-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _

  reflect-lc : is-stable → ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc S {n = n} p = ap fst (S (reflect n) (_ , p) (normal n))

