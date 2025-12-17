```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Dec where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Kan
open import Lib.Path
open import Lib.Sigma

data Dec {u} (A : Type u) : Type u where
  yes : A → Dec A
  no : ¬ A → Dec A

DecEq : ∀ {u} → Type u → Type u
DecEq A = (x y : A) → Dec (x ≡ y)

is-stable : ∀ {u} → Type u → Type u
is-stable A = ¬ (¬ A) → A

is-collapsible : ∀ {u} → Type u → Type u
is-collapsible A = Σ λ (f : A → A) → ∀ (x y : A) → f x ≡ f y

⊥-fp : (@0 x : ⊥) → x ≡ ex-falso x
⊥-fp = ⊥.ind (λ x → x ≡ ex-falso x)

⊥-is-prop : (@0 x y : ⊥) → x ≡ y
⊥-is-prop x = ex-falso x

module _ {u} {A : Type u} where
  not-is-prop : (@0 x y : ¬ A) → x ≡ y
  not-is-prop na na' i a = ⊥-is-prop (na a) (na' a) i

  dec→stable : Dec A → is-stable A
  dec→stable (yes a) _ = a
  dec→stable (no na) ¬¬a = ex-falso (¬¬a na)

  stable→collapsible : is-stable A → is-collapsible A
  stable→collapsible s .fst = λ a → s (λ na → na a)
  stable→collapsible s .snd = λ x y i → s (λ na → ⊥-is-prop (na x) (na y) i)

  collapsible-id→is-set : ((x y : A) → is-collapsible (x ≡ y)) → is-set A
  collapsible-id→is-set ρ x y p q = p≡q where
      -- Credit for this proof goes to agda-cubical Relations.Nullary.Properties
      f : {a : A} → x ≡ a → x ≡ a
      f {a} = ρ x a .fst

      Κ : {a : A} (s r : x ≡ a) → f s ≡ f r
      Κ {a} = ρ x a .snd

      H : (s : x ≡ y) → PathP (λ i → x ≡ s i) (f rfl) (f s)
      H s j = f {s j} (λ i → s (i ∧ j))

      p≡q : p ≡ q
      p≡q j i = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → f rfl k
        k (i = i1) → Κ p q j k
        k (j = i0) → H p i k
        k (j = i1) → H q i k
        k (k = i0) → x

hedberg : ∀ {u} {A : Type u} → DecEq A → is-set A
hedberg {A = A} d =
  let
    ρ : (x y : A) → is-collapsible (x ≡ y)
    ρ x y = stable→collapsible (dec→stable (d x y))
  in collapsible-id→is-set ρ
