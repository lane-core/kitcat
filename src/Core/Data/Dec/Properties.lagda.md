Hedberg's theorem: decidable equality implies set-truncatedness.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Dec.Properties where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Data.Sigma.Type using (fst; snd)
open import Core.Data.Dec.Type
open import Core.Data.Dec.Base

```

A type with collapsible identity types is a set. The proof constructs
a square witnessing `p = q` by composing the constant endomorphism on
paths against the filler of the collapsibility coherence.

```agda

-- Following Kraus, Escardo, Coquand, Altenkirch (LICS 2013)
collapsible-id→is-set
  : ∀ {u} {A : Type u}
  → ((x y : A) → is-collapsible (x ≡ y))
  → is-set A
collapsible-id→is-set {A = A} ρ x y p q = p≡q where
  f : {a : A} → x ≡ a → x ≡ a
  f {a} = ρ x a .fst

  Κ : {a : A} (s r : x ≡ a) → f s ≡ f r
  Κ {a} = ρ x a .snd

  H : (s : x ≡ y) → PathP (λ i → x ≡ s i) (f refl) (f s)
  H s j = f {s j} (λ i → s (i ∧ j))

  p≡q : p ≡ q
  p≡q j i = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → f refl k
    k (i = i1) → Κ p q j k
    k (j = i0) → H p i k
    k (j = i1) → H q i k
    k (k = i0) → x

hedberg : ∀ {u} {A : Type u} → DecEq A → is-set A
hedberg {A = A} d = collapsible-id→is-set ρ where
  ρ : (x y : A) → is-collapsible (x ≡ y)
  ρ x y = stable→collapsible (dec→stable (d x y))

```
