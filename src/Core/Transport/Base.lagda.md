Foundational transport, coercion, and the primitive `transp` operation.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Transport.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan

private module X where
  open import Agda.Primitive.Cubical public using (primTransp; primHComp)
open X public renaming (primTransp to transp) using () public

private
  variable
    ℓ : I → Level
    u : Level
    A : Type u
    U : I → Type u

```

## Coercion Family

The `coe` family provides convenient wrappers around `transp` for common coercion patterns.

```agda

module _ (A : ∀ i → Type (ℓ i)) where
  coe0i : (i : I) → A i0 → A i
  coe0i i = transp (∂.extend A i) (~ i)
  {-# INLINE coe0i #-}

  coe01 : A i0 → A i1
  coe01 = transp A i0
  {-# INLINE coe01 #-}

  coe10 : A i1 → A i0
  coe10 = transp (∂.sym A) i0
  {-# INLINE coe10 #-}

  coei1 : (i : I) → A i → A i1
  coei1 i = transp (∂.contract A i) i
  {-# INLINE coei1 #-}

  coei0 : (i : I) → A i → A i0
  coei0 i a = transp (∂.sym (∂.extend A i)) (~ i) a
  {-# INLINE coei0 #-}

  coe1i : (i : I) → A i1 → A i
  coe1i i = transp (∂.sym (∂.contract A i)) i
  {-# INLINE coe1i #-}

  coe : (i j : I) → A i → A j
  coe i j = transp (λ k → A (ierp k i j)) (ieq i j)
  {-# INLINE coe #-}

{-# DISPLAY transp A i0 = coe01 A #-}
{-# DISPLAY transp (∂.extend A i) _ = coe0i A i #-}
{-# DISPLAY transp (∂.contract A i) _ = coei1 A i #-}
{-# DISPLAY transp (∂.sym A) i0 = coe10 A #-}
{-# DISPLAY transp (∂.sym (∂.contract A i)) _ = coe1i A i #-}

```

## Transport

```agda

transport : ∀ {u} {A B : Type u} → A ≡ B → A → B
transport P = coe01 (λ i → P i)

transport-refl : ∀ {u} {A : Type u} (x : A) → transport {A = A} refl x ≡ x
transport-refl {A} x i = coe0i (λ _ → A) (~ i) x

transport⁻ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → B → A
transport⁻ P = coe01 (λ i → P (~ i))

```

## Singleton Contractibility

The contractibility of singleton types is fundamental to the J eliminator.

```agda

Singl-contr : ∀ {u} {A : Type u} (x : A) → is-contr (Σ y ∶ A , x ≡ y)
Singl-contr x .center = x , refl
Singl-contr x .paths (y , q) = λ i → (q i) , λ j → q (i ∧ j)

```

## Fillers

```agda

coe-filler : (A : I → Type u) (x : A i0) → PathP A x (coe01 A x)
coe-filler A x i = coe0i A i x

transport-filler : ∀ {u} {A B : Type u} (P : A ≡ B) (x : A) → PathP (λ i → P i) x (transport P x)
transport-filler P = coe-filler (λ i → P i)

module transp (A : I → Type u) where
  fill10 : (x : A i1) → PathP (λ i → A (~ i)) x (coe10 A x)
  fill10 x j = coe1i A (~ j) x

  fill0i : (x : A i0) (i : I) → PathP (λ j → A (i ∧ j)) x (coe0i A i x)
  fill0i x i j = coe0i A (i ∧ j) x

  fill1i : (x : A i1) (i : I) → PathP (λ j → A (i ∨ ~ j)) x (coe1i A i x)
  fill1i x i j = coe1i A (i ∨ ~ j) x

  filli : ∀ i x → coe A i i x ≡ x
  filli i x j = transp (λ _ → A i) (j ∨ i ∨ ~ i) x

  path : ∀ {ℓ} (A : I → Type ℓ) (p : ∀ i → A i) i j → coe A i j (p i) ≡ p j
  path A p i j k = transp (λ l → A (ierp k (ierp l i j) j)) (ierp k (ieq i j) i1) (p (ierp k i j))

```
