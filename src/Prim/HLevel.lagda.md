```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Prim.HLevel where

open import Prim.Type
open import Prim.Interval
open import Prim.Sub
open import Prim.Kan
open import Prim.Path
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

-- Credit for the following proofs goes to 1lab
is-contr→extend : ∀ {ℓ} {A : Type ℓ} → is-contr A
                → (i : I) (p : Partial i A) →  A [ i ↦ p ]
is-contr→extend contr i p = inS
  (hcomp (∂ i) λ where
      j (i = i1) → contr .paths (p 1=1) j
      j (i = i0) → contr .ctr
      j (j = i0) → contr .ctr)
{-# INLINE is-contr→extend #-}

extend→is-contr : ∀ {ℓ} {A : Type ℓ}
                → (∀ i (p : Partial i A) → A [ i ↦ p ])
                → is-contr A
extend→is-contr ex .ctr = outS (ex i0 λ ())
extend→is-contr ex .paths x i = outS (ex i (λ _ → x))

is-prop→PathP : ∀ {ℓ} {A : I → Type ℓ} → ((i : I) → is-prop (A i))
              → ∀ x y → PathP (λ i → A i) x y
is-prop→PathP {A} H x y = Path-over.to-pathp (H i1 (coe01 A x) y)

is-prop→SquareP : ∀ {ℓ} {B : I → I → Type ℓ}
                → ((i j : I) → is-prop (B i j))
                → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
                → (p : PathP (λ j → B i0 j) a b)
                → (q : PathP (λ i → B i i0) a c)
                → (r : PathP (λ j → B i1 j) c d)
                → (s : PathP (λ i → B i i1) b d)
                → SquareP B p q r s
is-prop→SquareP {B} bprop {a} p q r s i j =
  let base : (i j : I) → B i j
      base i j = coe01 (λ k → B (i ∧ k) (j ∧ k)) a
  in hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → bprop i0 j (base i0 j) (p j) k
    k (i = i1) → bprop i1 j (base i1 j) (r j) k
    k (j = i0) → bprop i i0 (base i i0) (q i) k
    k (j = i1) → bprop i i1 (base i i1) (s i) k
    k (k = i0) → base i j

is-prop→PathP-is-contr : ∀ {ℓ} {A : I → Type ℓ}
                       → ((i : I) → is-prop (A i))
                       → (x : A i0) (y : A i1)
                       → is-contr (PathP A x y)
is-prop→PathP-is-contr aprop x y .ctr = is-prop→PathP aprop x y
is-prop→PathP-is-contr {A = A} aprop x y .paths p =
  let
    α : PathP A x y
    α i = hcomp (∂ i) λ where
      j (i = i0) → x
      j (i = i1) → aprop i1 (coe01 A x) y j
      j (j = i0) → coe0i A i x
  in is-prop→SquareP (λ i j → aprop j) α refl p refl

is-contr→is-prop : ∀ {ℓ} {A : Type ℓ} → is-contr A → is-prop A
is-contr→is-prop contr x y i = outS do
  is-contr→extend contr (∂ i) λ where
    (i = i0) → x
    (i = i1) → y

inhab-to-contr→is-prop : ∀ {ℓ} {A : Type ℓ} → (A → is-contr A) → is-prop A
inhab-to-contr→is-prop iprop x y = is-contr→is-prop (iprop x) x y

is-contr→is-set : ∀ {ℓ} {A : Type ℓ} → is-contr A → is-set A
is-contr→is-set contr x y p q i j = outS do
  is-contr→extend contr (∂ i ∨ ∂ j) λ where
    (i = i0) → p j
    (i = i1) → q j
    (j = i0) → x
    (j = i1) → y

is-contr→PathP : ∀ {ℓ} {A : I → Type ℓ}
               → ((i : I) → is-contr (A i))
               → (a0 : A i0) (a1 : A i1)
               → PathP A a0 a1
is-contr→PathP contr = is-prop→PathP (λ i → is-contr→is-prop (contr i))

is-prop→is-set : ∀ {ℓ} {A : Type ℓ} → is-prop A → is-set A
is-prop→is-set aprop x = is-contr→is-set (contractible aprop x) x

is-prop-is-prop : ∀ {ℓ} (A : Type ℓ) → is-prop (is-prop A)
is-prop-is-prop A xprop yprop i x y = is-prop→is-set xprop x y (xprop x y) (yprop x y) i

is-contr-is-prop : ∀ {ℓ} (A : Type ℓ) → is-prop (is-contr A)
is-contr-is-prop A x y i .ctr =
  let φ = is-prop-is-prop A (is-contr→is-prop x) (is-contr→is-prop y) i
  in φ (x .ctr) (y .ctr) i
is-contr-is-prop A x y i .paths = β i
  where
  φ : is-prop A
  φ = is-prop-is-prop A (is-contr→is-prop x) (is-contr→is-prop y) i

  α : x .ctr ≡ y .ctr
  α = φ (x .ctr) (y .ctr)

  ψ : (k : I) (z : A) → (p q : α k ≡ z) → p ≡ q
  ψ k z p q = is-contr→is-set x (α k) z p q

  contr : (z : A) (k : I) → is-contr (α k ≡ z)
  contr z k = contractible (ψ k z) (φ (α k) z)

  β : (j : I) (z : A) → α j ≡ z
  β j z = is-contr→PathP (contr z) (x .paths z) (y .paths z) j
