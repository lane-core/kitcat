Advanced transport properties: contractibility, PathP lemmas, and identity systems.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Transport.Properties where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Sub
open import Core.Transport.Base
open import Core.Transport.J

private
  variable
    ℓ : I → Level
    u : Level
    A : Type u
    U : I → Type u

```

## Contractibility and Extension

Credit for the hlevel proofs throughout this module goes to 1lab.

```agda

is-contr→extend : ∀ {ℓ} {A : Type ℓ} → is-contr A
                → (i : I) (p : Partial i A) →  A [ i ↦ p ]
is-contr→extend c i p = inS do
  hcom (∂ i) λ where
      j (i = i1) → c .paths (p 1=1) j
      j (i = i0) → c .center
      j (j = i0) → c .center
{-# INLINE is-contr→extend #-}

extend→is-contr : ∀ {u} {A : Type u}
                → (∀ i (p : Partial i A) → A [ i ↦ p ])
                → is-contr A
extend→is-contr ex .center = outS do ex i0 λ ()
extend→is-contr ex .paths x i = outS do ex i (λ _ → x)

is-contr→is-prop : ∀ {u} {A : Type u} → is-contr A → is-prop A
is-contr→is-prop c x y i = outS do
  is-contr→extend c (∂ i) λ where
    (i = i0) → x
    (i = i1) → y

```

## Singleton Contractibility

```agda

Singl-unique : ∀ {u} {A : Type u} {x : A} → is-prop (Σ y ∶ A , x ≡ y)
Singl-unique {x} = is-contr→is-prop (Singl-contr x)

Cosingl-contr : ∀ {u} {A : Type u} (x : A) → is-contr (Σ y ∶ A , y ≡ x)
Cosingl-contr x .center = x , refl
Cosingl-contr x .paths (y , q) i = q (~ i) , λ j → q (~ i ∨ j)

Cosingl-unique : ∀ {u} {A : Type u} {x : A} → is-prop (Σ y ∶ A , y ≡ x)
Cosingl-unique {x} = is-contr→is-prop (Cosingl-contr x)

```

## Transport Composition

Transport-based composition. This is an alternative to hcom-based `_∙_`.

```agda

tcom : ∀ {u} {A : Type u} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
tcom {x = x} p q = transport (λ i → x ≡ q i) p

tcom-unitr : ∀ {u} {A : Type u} {x y : A} (p : x ≡ y) → tcom p refl ≡ p
tcom-unitr p = transport-refl p

module _ {u} {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) where
  tcom-filler : PathP (λ i → x ≡ q i) p (tcom p q)
  tcom-filler = transport-filler (λ i → x ≡ q i) p

  hcom≡tcom : (p ∙ q) ≡ tcom p q
  hcom≡tcom i j = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → cat.fill p q j k
    k (i = i1) → tcom-filler k j
    k (j = i0) → x
    k (j = i1) → q k
    k (k = i0) → p j

  tcom≡hcom : tcom p q ≡ (p ∙ q)
  tcom≡hcom = sym hcom≡tcom

subst-path-left : ∀ {u} {A : Type u} {a b c : A} (p : a ≡ b) (q : a ≡ c)
                → subst (_≡ c) p q ≡ sym p ∙ q
subst-path-left {c = c} p q = J (λ b' p' → subst (_≡ c) p' q ≡ sym p' ∙ q)
                                (transport-refl q ∙ sym (eqvl q))
                                p

```

## Inverse Transport

```agda

transport⁻-transport
  : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (b : B)
  → transport p (transport⁻ p b) ≡ b
transport⁻-transport p b j =
  transp (λ i → p (j ∨ i)) j (transp (λ i → p (j ∨ ~ i)) j b)

transport-transport⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (a : A)
                     → transport⁻ p (transport p a) ≡ a
transport-transport⁻ p a = transport⁻-transport (sym p) a

```

## PathP Conversions

```agda

Path-over : ∀ {u} (A : I → Type u) → A i0 → A i1 → Type u
Path-over A x y = coe01 A x ≡ y

module Path-over {u} {A : I → Type u} {x} {y} where
  to-pathp : Path-over A x y → PathP A x y
  to-pathp p i = hcom (∂ i) λ where
    j (i = i0) → x
    j (i = i1) → p j
    j (j = i0) → coe0i A i x

  from-pathp : PathP A x y → Path-over A x y
  from-pathp p i = coei1 A i (p i)

  eq-pathp : ∀ {ℓ} (P : I → Type ℓ) x y → PathP P x y ≡ Path-over P x y
  eq-pathp P x y i = PathP (∂.contract P i) (coe-filler P x i) y

is-prop→PathP : ∀ {u} {A : I → Type u} → ((i : I) → is-prop (A i))
              → ∀ x y → PathP (λ i → A i) x y
is-prop→PathP {A} H x y = Path-over.to-pathp do H i1 (coe01 A x) y

is-prop→SquareP : ∀ {u} {B : I → I → Type u}
                → ((i j : I) → is-prop (B i j))
                → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
                → (p : PathP (λ j → B i0 j) a b)
                → (q : PathP (λ i → B i i0) a c)
                → (r : PathP (λ j → B i1 j) c d)
                → (s : PathP (λ i → B i i1) b d)
                → SquareP B p q r s
is-prop→SquareP {B} prop {a} p q r s i j =
  let base : (i j : I) → B i j
      base i j = coe01 (λ k → B (i ∧ k) (j ∧ k)) a
  in hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → prop i0 j (base i0 j) (p j) k
    k (i = i1) → prop i1 j (base i1 j) (r j) k
    k (j = i0) → prop i i0 (base i i0) (q i) k
    k (j = i1) → prop i i1 (base i i1) (s i) k
    k (k = i0) → base i j

SinglP-contr : ∀ {u} {A : I → Type u} (x : A i0)
             → is-contr (Σ y ∶ A i1 , PathP A x y)
SinglP-contr {A} x .center = coe01 A x , coe-filler A x
SinglP-contr {A} x .paths (y , q) i = _ , λ j → fil A (∂ i) j λ where
 j (i = i0) → coe0i A j x
 j (j = i0) → x
 j (i = i1) → q j

TotalP
  : ∀ {u v} {A : Type u} {B : A → Type v} {x} (a : B x)
  → is-contr (Σ y ∶ A , Σ q ∶ (x ≡ y) , Σ b ∶ B y , PathP (λ i → B (q i)) a b)
TotalP {x} a .center = x , refl , a , refl
TotalP a .paths (y , q , b , α) i = q i , (λ j → q (i ∧ j)) , α i , λ j → α (i ∧ j)

is-prop→PathP-is-contr : ∀ {u} {A : I → Type u}
                       → ((i : I) → is-prop (A i))
                       → (x : A i0) (y : A i1)
                       → is-contr (PathP A x y)
is-prop→PathP-is-contr aprop x y .center = is-prop→PathP aprop x y
is-prop→PathP-is-contr {A = A} aprop x y .paths p =
  let
    α : PathP A x y
    α i = hcom (∂ i) λ where
      j (i = i0) → x
      j (i = i1) → aprop i1 (coe01 A x) y j
      j (j = i0) → coe0i A i x
  in is-prop→SquareP (λ i j → aprop j) α refl p refl

```

## H-Level Properties

```agda

inhab-to-contr→is-prop : ∀ {u} {A : Type u} → (A → is-contr A) → is-prop A
inhab-to-contr→is-prop iprop x y = is-contr→is-prop (iprop x) x y

is-contr→is-set : ∀ {u} {A : Type u} → is-contr A → is-set A
is-contr→is-set c x y p q i j = outS do
  is-contr→extend c (∂ i ∨ ∂ j) λ where
    (i = i0) → p j
    (i = i1) → q j
    (j = i0) → x
    (j = i1) → y

is-contr→loop-is-refl
  : ∀ {u} {A : Type u} (c : is-contr A) → c .paths (c .center) ≡ refl
is-contr→loop-is-refl c =
  is-contr→is-set c _ _ (c .paths (c .center)) refl

is-contr→PathP : ∀ {u} {A : I → Type u}
               → ((i : I) → is-contr (A i))
               → (a0 : A i0) (a1 : A i1)
               → PathP A a0 a1
is-contr→PathP c = is-prop→PathP (λ i → is-contr→is-prop (c i))

is-prop→is-set : ∀ {u} {A : Type u} → is-prop A → is-set A
is-prop→is-set aprop x = is-contr→is-set (Contr x (aprop x)) x

is-prop-is-prop : ∀ {u} (A : Type u) → is-prop (is-prop A)
is-prop-is-prop A xprop yprop i x y =
  is-prop→is-set xprop x y (xprop x y) (yprop x y) i

-- Credit for most of the following proofs goes to 1lab
prop-inhabited→is-contr : ∀ {u} {A : Type u} → is-prop A → A → is-contr A
prop-inhabited→is-contr p c .center = c
prop-inhabited→is-contr p c .paths = p c

is-contr-is-prop : ∀ {u} (A : Type u) → is-prop (is-contr A)
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

  c : (z : A) (k : I) → is-contr (α k ≡ z)
  c z k = prop-inhabited→is-contr (ψ k z) (φ (α k) z)

  β : (j : I) (z : A) → α j ≡ z
  β j z = is-contr→PathP (c z) (x .paths z) (y .paths z) j

weak-funext : ∀ {u v} {A : Type u} {B : A → Type v}
            → ((x : A) → is-contr (B x))
            → is-contr ((x : A) → B x)
weak-funext all-contr .center x = all-contr x .center
weak-funext all-contr .paths f i x = all-contr x .paths (f x) i

is-contr-× : ∀ {u v} {A : Type u} {B : Type v}
           → is-contr A → is-contr B → is-contr (A × B)
is-contr-× cA cB .center = cA .center , cB .center
is-contr-× cA cB .paths (a , b) i = cA .paths a i , cB .paths b i

```

## Identity Systems

The fundamental theorem of identity types (Rijke Section 15): A reflexive relation
R with contractible total space at each point is an identity system. This is
precisely `singl-contr→Ids` below.

```agda

record is-identity-system {ℓ ℓ'} {A : Type ℓ}
  (R : A → A → Type ℓ')
  (refl : ∀ a → R a a)
  : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  field
    to-path      : ∀ {a b} → R a b → a ≡ b
    to-path-over
      : ∀ {a b} (p : R a b)
      → PathP (λ i → R a (to-path p i)) (refl a) p

  is-contr-ΣR : ∀ {a} → is-contr (Σ (R a))
  is-contr-ΣR .center    = _ , refl _
  is-contr-ΣR .paths x i = to-path (x .snd) i , to-path-over (x .snd) i

open is-identity-system public
{-# INLINE is-identity-system.constructor #-}

IdsJ
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → is-identity-system R r
  → (P : ∀ b → R a b → Type ℓ'')
  → P a (r a)
  → ∀ {b} s → P b s
IdsJ ids P pr s =
  transport (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr

-- The fundamental theorem of identity types (Rijke, Theorem 15.2.1):
-- If R is a reflexive relation with contractible total space Σ (R a) at each
-- point a, then R is an identity system.
singl-contr→Ids
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  → (∀ {a} → is-contr (Σ (R a)))
  → is-identity-system R r
singl-contr→Ids {R = R} {r} c = ids where
  paths' : ∀ {a} (p : Σ (R a)) → (a , r a) ≡ p
  paths' _ = is-contr→is-prop c _ _

  ids : is-identity-system R r
  ids .to-path p = ap fst (paths' (_ , p))
  ids .to-path-over p = ap snd (paths' (_ , p))

-- Alias for clarity: the fundamental theorem of identity types
-- This version takes an explicit (a : A) argument
fundamental-theorem-id
  : ∀ {u v} {A : Type u} {R : A → A → Type v} {r : ∀ a → R a a}
  → (∀ a → is-contr (Σ b ∶ A , R a b))
  → is-identity-system R r
fundamental-theorem-id c = singl-contr→Ids (c _)

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
{-# INLINE is-based-identity-system.constructor #-}

is-contr-ΣC
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → is-based-identity-system a C r
  → is-contr (Σ C)
is-contr-ΣC {r = r} ids .center         = _ , r
is-contr-ΣC {r = r} ids .paths x i .fst = ids .to-path (x .snd) i
is-contr-ΣC {r = r} ids .paths x i .snd = ids .to-path-over (x .snd) i

IdsJ-based
  : ∀ {u u' u''} {A : Type u} {a : A} {C : A → Type u'} {r : C a}
  → is-based-identity-system a C r
  → (P : ∀ b → C b → Type u'')
  → P a r
  → ∀ {b} s → P b s
IdsJ-based ids P pr s = transport
  (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr

set-identity-system
  : ∀ {u u'} {A : Type u} {R : A → A → Type u'} {r : ∀ x → R x x}
  → (∀ x y → is-prop (R x y))
  → (∀ {x y} → R x y → x ≡ y)
  → is-identity-system R r
set-identity-system rprop rpath .to-path = rpath
set-identity-system rprop rpath .to-path-over p =
  is-prop→PathP (λ i → rprop _ _) _ p

```
