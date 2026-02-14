Path composition structures and higher coherences.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Composite where

open import Core.Transport
open import Core.HLevel
open import Core.Base
open import Core.Type
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub

private variable
  ℓ : Level
  u v : Level
  A : Type u

```
## Heterogeneous System Operations

Operations on systems for type families varying over I.
```agda

module HSysOps {A : I → Type u} (φ : I) (s : PartialsP φ A) where
  hsys-base : A i0
  hsys-base = s i0 1=1

  hsys-filler : (i : I) → A i
  hsys-filler i = com (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
    k (φ = i1) → s (i ∧ k) 1=1
    k (i = i0) → hsys-base
    k (k = i0) → hsys-base

  hsys-composite : A i1
  hsys-composite = hsys-filler i1

  hsys-path : PathP A hsys-base hsys-composite
  hsys-path i = hsys-filler i

```
## Dependent Systems (SysP)

Systems over the sys-filler of a base system.
```agda

module SysP {u v} {A : Type u} (P : A → Type v) where
  SysOver : (φ : I) (s : Sys φ A) → Exo v
  SysOver φ s = (i : I) → Partial (φ ∨ ~ i) (P (sys-filler φ s i))

  baseP : (φ : I) (s : Sys φ A) → SysOver φ s → P (sys-base φ s)
  baseP φ s t = t i0 1=1

  fillerP : (φ : I) (s : Sys φ A) (t : SysOver φ s) (i : I) → P (sys-filler φ s i)
  fillerP φ s t i = com (λ j → P (sys-filler φ s (i ∧ j))) (φ ∨ ~ i) λ where
    k (φ = i1) → t (i ∧ k) 1=1
    k (i = i0) → baseP φ s t
    k (k = i0) → baseP φ s t

  compositeP : (φ : I) (s : Sys φ A) → SysOver φ s → P (sys-composite φ s)
  compositeP φ s t = fillerP φ s t i1

  pathP : (φ : I) (s : Sys φ A) (t : SysOver φ s)
        → PathP (λ i → P (sys-filler φ s i)) (baseP φ s t) (compositeP φ s t)
  pathP φ s t i = fillerP φ s t i

  SysLift : {x y : A} → x ≡ y → P x → Type v
  SysLift {x} {y} p a = Σ b ∶ P y , PathP (λ i → P (p i)) a b

  syslift-center : {x y : A} (p : x ≡ y) (a : P x) → SysLift p a
  syslift-center p a = transport (λ i → P (p i)) a , transport-filler (λ i → P (p i)) a

```
## System Functoriality

Functorial action on systems, preserving composition structure.
```agda

module SysFunctor {u v} {A : Type u} {B : Type v} (f : A → B) where
  map : (φ : I) → Sys φ A → Sys φ B
  map φ s i p = f (s i p)

  map-base : (φ : I) (s : Sys φ A) → sys-base φ (map φ s) ≡ f (sys-base φ s)
  map-base φ s = refl

  map-composite : (φ : I) (s : Sys φ A)
                → sys-composite φ (map φ s) ≡ f (sys-composite φ s)
  map-composite φ s i = hcom (φ ∨ i) λ where
    k (φ = i1) → f (s (i ∨ k) 1=1)
    k (i = i1) → f (sys-filler φ s (k ∨ φ))
    k (k = i0) → f (sys-filler φ s (i ∧ φ))

```
## Mode Transitions and Associativity

Associativity is the functorial transition between fill modes:
- At k=0: fully in T-mode for (p,q), identity for (q,r)
- At k=1: identity for (p,q), fully in L-mode for (q,r)
```agda

module ModeTransition {v w x y z : A}
  (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z) where

  lhs : p ∙ (q ∙ (r ∙ s)) ≡ ((p ∙ q) ∙ r) ∙ s
  lhs = Path.assoc p q (r ∙ s) ∙ Path.assoc (p ∙ q) r s

  rhs : p ∙ (q ∙ (r ∙ s)) ≡ ((p ∙ q) ∙ r) ∙ s
  rhs = (λ j → p ∙ Path.assoc q r s j) ∙ Path.assoc p (q ∙ r) s ∙ (λ j → Path.assoc p q r j ∙ s)

pentagon-lhs : {v w x y z : A} (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z)
             → p ∙ (q ∙ (r ∙ s)) ≡ ((p ∙ q) ∙ r) ∙ s
pentagon-lhs p q r s = ModeTransition.lhs p q r s

pentagon-rhs : {v w x y z : A} (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z)
             → p ∙ (q ∙ (r ∙ s)) ≡ ((p ∙ q) ∙ r) ∙ s
pentagon-rhs p q r s = ModeTransition.rhs p q r s

```
## Square Manipulation
```agda

lpush : {w x y z : A}
      → (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
      → Square p q r s → Square (λ _ → x) q r (p ∙ s)
lpush {x} p q r s sq i j = hcom (∂ i ∨ ~ j) λ where
  k (i = i0) → x
  k (j = i0) → q (i ∧ k)
  k (i = i1) → sq k j
  k (k = i0) → p (i ∧ j)

rpush : {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
      → Square p q r s → Square p (λ _ → x) (q ∙ r) s
rpush {x} p q r s sq i j = hcom (∂ j ∨ ~ i) λ where
  k (j = i0) → x
  k (i = i0) → p (j ∧ k)
  k (j = i1) → sq i k
  k (k = i0) → q (i ∧ j)

rpop : {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
     → Square p (λ _ → x) (q ∙ r) s → Square p q r s
rpop p q r s sq i j = hcom (∂ i ∨ ∂ j) λ where
  k (i = i0) → p j
  k (i = i1) → cat.bfill q r j k
  k (j = i0) → q (i ∧ k)
  k (j = i1) → s i
  k (k = i0) → sq i j

```
## Heterogeneous Connection
```agda

hconn : {A : I → Type u} {x y : A i0} {z : A i1}
     → (p : x ≡ y) (q : y ≡ z ∶ A)
     → SquareP (λ i j → A (i ∧ j)) p p q q
hconn {A} {y} {z} p q i j = hcom (∂ i ∨ ∂ j) sys
  module hconn where
    sys : Sys (∂ i ∨ ∂ j) (A (i ∧ j))
    sys k (k = i0) = q (i ∧ j)
    sys k (i = i0) = p (j ∨ ~ k)
    sys k (j = i0) = p (i ∨ ~ k)
    sys k (j = i1) = q i
    sys k (i = i1) = q j
{-# DISPLAY hcom _ (hconn.sys p q i j) = hconn p q i j #-}

```
## Equational Reasoning
```agda

begin_ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ p = p

_≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = sym p ∙ q

_∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
x ∎ = refl

infix  1 begin_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
infix  3 _∎

```
## Higher Loop Operations
```agda

loop-over : ∀ {u v} {A : Type u} (P : A → Type v)
          → {x y : A} (q : x ≡ y) (b : P y)
          → PathP (λ i → P ((sym q ∙ q) i)) b b
loop-over P q b i = hcom (∂ i) λ where
  k (i = i0) → transport-refl b k
  k (k = i0) → transport (λ j → P (Path.invl q (~ j) i)) b
  k (i = i1) → transport-refl b k

sym-loop : ∀ {u v} {A : Type u} (P : A → Type v) {x y : A}
         → (q : x ≡ y) {a b : P y}
         → PathP (λ i → P ((sym q ∙ q) i)) a b
         → a ≡ b
sym-loop P q {a} {b} α = transport (λ i → PathP (λ j → P (Path.invl q i j)) a b) α

```
