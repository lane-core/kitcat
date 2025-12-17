```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Lib.Core.HLevel where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Sub
open import Lib.Core.Kan
open import Lib.Core.Path
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
--open import Lib.Path.Gpd

record Tr : Type where
  constructor hlevel
  field
    level : Nat

record N-type ℓ n : Type₊ ℓ where
  no-eta-equality
  field
    ∣_∣ : Type ℓ
    trunc : is-hlevel n ∣_∣

module _ {u v} {A : Type u} {B : Type v} where
  injective : (A → B) → Type _
  injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  injective→is-embedding
    : is-set B → (f : A → B) → injective f
    → ∀ x → is-prop (fiber f x)
  injective→is-embedding bset f inj x (f*x , p) (f*x' , q) =
    Σ-prop-path (λ x → bset _ _) (inj (p ∙ sym q))

  has-prop-fibres→injective
    : (f : A → B) → (∀ x → is-prop (fiber f x))
    → injective f
  has-prop-fibres→injective f prop {x} {y} p =
    ap fst (prop (f y) (x , p) (y , refl))

  is-embedding : (A → B) → Type _
  is-embedding f = ∀ x → is-prop (fiber f x)

_↪_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ↪ B = Σ f ∶ (A → B) , is-embedding f



-- Credit for the following proofs goes to 1lab
is-contr→extend : ∀ {ℓ} {A : Type ℓ} → is-contr A
                → (i : I) (p : Partial i A) →  A [ i ↦ p ]
is-contr→extend contr i p = inS do
  hcomp (∂ i) λ where
      j (i = i1) → contr .paths (p 1=1) j
      j (i = i0) → contr .ctr
      j (j = i0) → contr .ctr
{-# INLINE is-contr→extend #-}

extend→is-contr : ∀ {ℓ} {A : Type ℓ}
                → (∀ i (p : Partial i A) → A [ i ↦ p ])
                → is-contr A
extend→is-contr ex .ctr = outS do ex i0 λ ()
extend→is-contr ex .paths x i = outS do ex i (λ _ → x)

is-prop→PathP : ∀ {ℓ} {A : I → Type ℓ} → ((i : I) → is-prop (A i))
              → ∀ x y → PathP (λ i → A i) x y
is-prop→PathP {A} H x y = Path-over.to-pathp do H i1 (coe01 A x) y

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
  in is-prop→SquareP (λ i j → aprop j) α rfl p rfl

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

-- Credit for most of the following proofs goes to 1lab
is-contr→extend : ∀ {ℓ} {A : Type ℓ} → is-contr A → (i : I) (p : Partial i A) →  A [ i ↦ p ]
is-contr→extend contract i p = inS do
  hcomp (∂ i) λ where
      j (i = i1) → contract .paths (p 1=1) j
      j (i = i0) → contract .center
      j (j = i0) → contract .center
{-# INLINE is-contr→extend #-}

extend→is-contr : ∀ {ℓ} {A : Type ℓ}
                → (∀ i (p : Partial i A) → A [ i ↦ p ])
                → is-contr A
extend→is-contr ex .center = outS do ex i0 λ ()
extend→is-contr ex .paths x i = outS do ex i (λ _ → x)

is-prop→PathP : ∀ {ℓ} {A : I → Type ℓ} → ((i : I) → is-prop (A i))
              → ∀ x y → PathP (λ i → A i) x y
is-prop→PathP {A} H x y = Path-over.to-pathp do H i1 (coe01 A x) y

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
is-prop→PathP-is-contr aprop x y .center = is-prop→PathP aprop x y
is-prop→PathP-is-contr {A = A} aprop x y .paths p =
  let
    α : PathP A x y
    α i = hcomp (∂ i) λ where
      j (i = i0) → x
      j (i = i1) → aprop i1 (coe01 A x) y j
      j (j = i0) → coe0i A i x
  in is-prop→SquareP (λ i j → aprop j) α refl p refl

is-contr→is-prop : ∀ {ℓ} {A : Type ℓ} → is-contr A → is-prop A
is-contr→is-prop c x y i = outS do
  is-contr→extend c (∂ i) λ where
    (i = i0) → x
    (i = i1) → y

inhab-to-contr→is-prop : ∀ {ℓ} {A : Type ℓ} → (A → is-contr A) → is-prop A
inhab-to-contr→is-prop iprop x y = is-contr→is-prop (iprop x) x y

prop-inhabited→is-contr : {A : Type u} → is-prop A → A → is-contr A
prop-inhabited→is-contr p c .center = c
prop-inhabited→is-contr p c .paths = p c

is-contr→is-set : ∀ {ℓ} {A : Type ℓ} → is-contr A → is-set A
is-contr→is-set c x y p q i j = outS do
  is-contr→extend c (∂ i ∨ ∂ j) λ where
    (i = i0) → p j
    (i = i1) → q j
    (j = i0) → x
    (j = i1) → y

is-contr→PathP : ∀ {ℓ} {A : I → Type ℓ}
               → ((i : I) → is-contr (A i))
               → (a0 : A i0) (a1 : A i1)
               → PathP A a0 a1
is-contr→PathP c = is-prop→PathP (λ i → is-contr→is-prop (c i))

is-prop→is-set : ∀ {ℓ} {A : Type ℓ} → is-prop A → is-set A
is-prop→is-set aprop x = is-contr→is-set (prop-inhabited→is-contr aprop x) x

is-prop-is-prop : ∀ {ℓ} (A : Type ℓ) → is-prop (is-prop A)
is-prop-is-prop A xprop yprop i x y = is-prop→is-set xprop x y (xprop x y) (yprop x y) i

is-contr-is-prop : ∀ {ℓ} (A : Type ℓ) → is-prop (is-contr A)
is-contr-is-prop A x y i .center =
  let φ = is-prop-is-prop A (is-contr→is-prop x) (is-contr→is-prop y) i
  in φ (x .center) (y .center) i
is-contr-is-prop A x y i .paths = β i
  where
  φ : is-prop A
  φ = is-prop-is-prop A (is-contr→is-prop x) (is-contr→is-prop y) i

  α : x .center ≡ y .center
  α = φ (x .center) (y .center)

  ψ : (k : I) (z : A) → (p q : α k ≡ z) → p ≡ q
  ψ k z p q = is-contr→is-set x (α k) z p q

  contract : (z : A) (k : I) → is-contr (α k ≡ z)
  contract z k = prop-inhabited→is-contr (ψ k z) (φ (α k) z)

  β : (j : I) (z : A) → α j ≡ z
  β j z = is-contr→PathP (contract z) (x .paths z) (y .paths z) j

Σ-prop-path
  : ∀ {u v} {A : Type u} {B : A → Type v} (bp : ∀ x → is-prop (B x))
  → {x y : Σ B}
  → (x .fst ≡ y .fst) → x ≡ y
Σ-prop-path bp {x} {y} p i =
  p i , is-prop→PathP (λ i → bp (p i)) (x .snd) (y .snd) i

subst-prop : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} → is-prop A → ∀ a → P a → ∀ b → P b
subst-prop {P = P} prop a pa b = subst P (prop a b) pa

```
I want to do my own spin on identity systems, but until then shamelessly copied
from the excellent 1lab
```
record is-identity-system {ℓ ℓ'} {A : Type ℓ}
  (R : A → A → Type ℓ')
  (refl : ∀ a → R a a)
  : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  field
    to-path      : ∀ {a b} → R a b → a ＝ b
    to-path-over
      : ∀ {a b} (p : R a b)
      → PathP (λ i → R a (to-path p i)) (refl a) p

  is-contr-ΣR : ∀ {a} → is-contr (Σ (R a))
  is-contr-ΣR .center    = _ , refl _
  is-contr-ΣR .paths x i = to-path (x .snd) i , to-path-over (x .snd) i

open is-identity-system public

IdsJ
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → is-identity-system R r
  → (P : ∀ b → R a b → Type ℓ'')
  → P a (r a)
  → ∀ {b} s → P b s
IdsJ ids P pr s =
  transport (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr

contr→identity-system
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  → (∀ {a} → is-contr (Σ (R a)))
  → is-identity-system R r
contr→identity-system {R = R} {r} c = ids where
  paths' : ∀ {a} (p : Σ (R a)) → (a , r a) ≡ p
  paths' _ = is-contr→is-prop c _ _

  ids : is-identity-system R r
  ids .to-path p = ap fst (paths' (_ , p))
  ids .to-path-over p = ap snd (paths' (_ , p))

record
  is-based-identity-system {ℓ ℓ'} {A : Type ℓ}
    (a : A)
    (C : A → Type ℓ')
    (refl : C a)
    : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  field
    to-path : ∀ {b} → C b → a ≡ b
    to-path-over
      : ∀ {b} (p : C b)
      → PathP (λ i → C (to-path p i)) refl p

open is-based-identity-system public

is-contr-ΣC
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → is-based-identity-system a C r
  → is-contr (Σ C)
is-contr-ΣC {r = r} ids .center         = _ , r
is-contr-ΣC {r = r} ids .paths x i .fst = ids .to-path (x .snd) i
is-contr-ΣC {r = r} ids .paths x i .snd = ids .to-path-over (x .snd) i

IdsJ-based
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → is-based-identity-system a C r
  → (P : ∀ b → C b → Type ℓ'')
  → P a r
  → ∀ {b} s → P b s
IdsJ-based ids P pr s = transport
  (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr

set-identity-system
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ x → R x x}
  → (∀ x y → is-prop (R x y))
  → (∀ {x y} → R x y → x ≡ y)
  → is-identity-system R r
set-identity-system rprop rpath .to-path = rpath
set-identity-system rprop rpath .to-path-over p =
  is-prop→PathP (λ i → rprop _ _) _ p
