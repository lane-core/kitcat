Properties and lemmas for natural numbers.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Nat.Properties where

open import Core.Base
open import Core.Type
open import Core.Kan hiding (assoc)
open import Core.Transport
open import Core.Data.Dec
open Dec
open import Core.Data.Empty
open import Core.Data.Sum
open import Core.Data.Nat.Type
open import Core.Data.Nat.Base

private variable
  m n k : Nat

```

Ordering lemmas.

```agda

module lt where
  open Core.Data.Nat.Base using (s<s) public

  z<s : Z < S n
  z<s {n = Z} = suc
  z<s {n = S n} = step z<s

  peel : ∀ n → S m < S n → m < n
  peel (S m) suc = suc
  peel (S n) (step p) = step (peel n p)

  ¬n<z : ∀ {n} → ¬ (n < Z)
  ¬n<z ()

  cat : ∀ {k} → m < n → n < k → m < k
  cat {k = Z} p q = ex-falso (¬n<z q)
  cat {k = S k} p suc = step p
  cat {k = S k} p (step q) = step (cat p q)

  irrefl : ∀ {n} → n < n → ⊥
  irrefl {n = S n} (step p) = irrefl (peel n (step p))

  <→z< : ∀ {i j} → i < j → Z < j
  <→z< {j = S _} _ = z<s

  instance
    z<s-irr : ∀ {n} → Irr (Z < (S n))
    z<s-irr = forget z<s

lt-le-cat : ∀ {k m n} → k < m → m ≤ n → k < n
lt-le-cat p suc = p
lt-le-cat p (step q) = lt.cat p q

lt-le-absurd : ∀ {a b} → a < b → b ≤ a → ⊥
lt-le-absurd p q = lt.irrefl (lt-le-cat p q)

le-lt-pred : ∀ {j i k} → j ≤ i → i < k → j ≤ pred k
le-lt-pred {k = S k'} ji ik = lt-le-cat ji (s<s ik)

cmp : (m n : Nat) → (m < S n) ⊎ (n < m)
cmp Z _ = inl lt.z<s
cmp (S m) Z = inr lt.z<s
cmp (S m) (S n) with cmp m n
... | inl p = inl (s<s p)
... | inr q = inr (s<s q)

module le where
  rx : n ≤ n
  rx = suc

  cat : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  cat suc = id
  cat (step p) = lt.cat p

  pred-mono : ∀ {a b} → a ≤ b → pred a ≤ pred b
  pred-mono {a = Z} _ = lt.z<s
  pred-mono {a = S a} {b = Z} p = ex-falso (lt-le-absurd lt.z<s p)
  pred-mono {a = S a} {b = S b} p = lt.peel (S b) p

```

Arithmetic lemmas.

```agda

module add where
  unitr : ∀ n → n + Z ≡ n
  unitr Z = refl
  unitr (S n) = ap S (unitr n)

  +suc : ∀ m n → m + S n ≡ S (m + n)
  +suc Z n = refl
  +suc (S m) n = ap S (+suc m n)

  comm : ∀ m n → m + n ≡ n + m
  comm Z n = sym (unitr n)
  comm (S m) n = ap S (comm m n) ∙ sym (+suc n m)

  assoc : ∀ m n k → m + (n + k) ≡ (m + n) + k
  assoc Z n k = refl
  assoc (S m) n k = ap S (assoc m n k)

distr : ∀ m n k → (m + n) * k ≡ m * k + n * k
distr Z n k = refl
distr (S m) n k = ap (k +_) (distr m n k)
  ∙ add.assoc k (m * k) (n * k)

module mul where
  zeror : ∀ n → n * Z ≡ Z
  zeror Z = refl
  zeror (S n) = zeror n

  *suc : ∀ m n → m * S n ≡ m + m * n
  *suc Z n = refl
  *suc (S m) n =
    ap (S n +_) (*suc m n)
    ∙ ap S (add.assoc n m (m * n)
      ∙ ap (_+ m * n) (add.comm n m)
      ∙ sym (add.assoc m n (m * n)))

  comm : ∀ m n → m * n ≡ n * m
  comm Z n = sym (zeror n)
  comm (S m) n = ap (n +_) (comm m n) ∙ sym (*suc n m)

  assoc : ∀ m n k → m * (n * k) ≡ (m * n) * k
  assoc Z n k = refl
  assoc (S m) n k = ap (n * k +_) (assoc m n k)
    ∙ sym (distr n (m * n) k)

  unitl : ∀ n → S Z * n ≡ n
  unitl n = add.unitr n

  unitr : ∀ n → n * S Z ≡ n
  unitr n = *suc n Z ∙ ap (n +_) (zeror n) ∙ add.unitr n

distl : ∀ m n k → m * (n + k) ≡ m * n + m * k
distl m n k =
  mul.comm m (n + k)
  ∙ distr n k m
  ∙ ap (_+ k * m) (mul.comm n m)
  ∙ ap (m * n +_) (mul.comm k m)

module sub where
  -- facts about _-_ go here

```

Nat is a set (h-level 2).

```agda

DecEq-Nat : (m n : Nat) → Dec (m ≡ n)
DecEq-Nat Z Z = yes refl
DecEq-Nat Z (S _) = no (λ p → subst f p tt) where f = λ { Z → ⊤ ; (S _) → ⊥ }
DecEq-Nat (S _) Z = no (λ p → subst f p tt) where f = λ { Z → ⊥ ; (S _) → ⊤ }
DecEq-Nat (S m) (S n) with DecEq-Nat m n
... | yes p = yes (ap S p)
... | no ¬p = no λ q → ¬p (ap pred q)

set : is-set Nat
set = hedberg DecEq-Nat
