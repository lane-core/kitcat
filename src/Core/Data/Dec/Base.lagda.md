Basic lemmas on decidable types.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Dec.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Empty
open import Core.Data.Sigma.Type using (fst; snd)
open import Core.Data.Dec.Type

⊥-fp : (@0 x : ⊥) → x ≡ ex-falso x
⊥-fp = Void.ind (λ x → x ≡ ex-falso x)

⊥-is-prop : (@0 x y : ⊥) → x ≡ y
⊥-is-prop x = ex-falso x

module _ {u} {A : Type u} where
  not-is-prop : (@0 x y : ¬ A) → x ≡ y
  not-is-prop na na' i a = ⊥-is-prop (na a) (na' a) i

  Dec-is-prop : is-prop A → is-prop (Dec A)
  Dec-is-prop pA (yes a₁) (yes a₂) = ap yes (pA a₁ a₂)
  Dec-is-prop pA (yes a)  (no ¬a)  = ex-falso (¬a a)
  Dec-is-prop pA (no ¬a)  (yes a)  = ex-falso (¬a a)
  Dec-is-prop pA (no ¬a₁) (no ¬a₂) = ap no (not-is-prop ¬a₁ ¬a₂)

  dec→stable : Dec A → is-stable A
  dec→stable (yes a) _ = a
  dec→stable (no na) ¬¬a = ex-falso (¬¬a na)

  stable→collapsible : is-stable A → is-collapsible A
  stable→collapsible s .fst = λ a → s (λ na → na a)
  stable→collapsible s .snd =
    λ x y i → s (λ na → ⊥-is-prop (na x) (na y) i)

```
