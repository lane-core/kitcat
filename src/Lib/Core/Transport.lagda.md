```agda

{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Transport where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Type
open import Lib.Core.Kan
open import Lib.Core.Sub

-- Credit for the hlevel proofs throughout this module goes to 1lab
is-contr→extend : ∀ {ℓ} {A : Type ℓ} → is-contr A
                → (i : I) (p : Partial i A) →  A [ i ↦ p ]
is-contr→extend c i p = inS do
  hcomp (∂ i) λ where
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


Singl-contr : ∀ {u} {A : Type u} (x : A) → is-contr (Σ y ∶ A , x ≡ y)
Singl-contr x .center = x , refl
Singl-contr x .paths (y , q) = λ i → (q i) , λ j → q (i ∧ j)

Singl-unique : ∀ {u} {A : Type u} {x : A} → is-prop (Σ y ∶ A , x ≡ y)
Singl-unique {x} = is-contr→is-prop (Singl-contr x)

private
  variable
    ℓ : I → Level
    u : Level
    A : Type u
    U : I → Type u

private module X where
  open import Agda.Primitive.Cubical public using (primTransp; primHComp)
open X public renaming (primTransp to transp) using () public
-- primHComp  : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A
```
Recall from the Base module:

module ∂ where
  contract : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → Type (ℓ (i ∨ j))
  contract A i j = A (i ∨ j)
  {-# INLINE contract #-}

  extend : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → Type (ℓ (i ∧ j))
  extend A i j = A (i ∧ j)
  {-# INLINE extend #-}

  cover : {@0 ℓ : I → Level} {@0 A : ∀ i → Type (ℓ i)}
        → (φ : I)
        → (P : ∀ k → A (φ ∧ k) → Type (ℓ (φ ∧ k)))
        → (∀ k → A k)
        → (i : I) → Type (ℓ (φ ∧ i))
  cover φ P f i = P (φ ∧ i) (f (φ ∧ i))
  {-# INLINE cover #-}

  sym : {@0 ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → Type (ℓ (~ i))
  sym A i = A (~ i)
  {-# INLINE sym #-}

  line : ∀ {u v} {@0 A : I → Type u}
       → (P : ∀ {i} → A i → Type v)
       → ∀ {@0 x y} → PathP A x y
       → (i : I) → Type v
  line P q i = P (q i)
  {-# INLINE line #-}

  square : ∀ {u v} {A : I → Type u}
         → (P : {i : I} → A i → A i → Type v)
         → {x x' : A i0} {y y' : A i1}
         → PathP A x y → PathP A x' y'
         → (i : I) → Type v
  square R f g i = R (f i) (g i)
  {-# INLINE square #-}

  cube : ∀ {u v} {A : I → I → Type u}
       → (P : {i j : I} → A i j → A i j → Type v)
       → {x x' : ∀ i → A i i0} {y y' : ∀ i → A i i1}
       → (p : PathP (A i0) (x i0) (y i0))
       → (p' : PathP (A i0) (x' i0) (y' i0))
       → (q : PathP (A i1) (x i1) (y i1))
       → (q' : PathP (A i1) (x' i1) (y' i1))
       → PathP (λ i → PathP (λ j → A i j) (x i) (y i)) p q
       → PathP (λ i → PathP (λ j → A i j) (x' i) (y' i)) p' q'
       → (i j : I) → Type v
  cube P p p' q q' f g i j = P (f i j) (g i j)
  {-# INLINE cube #-}

```

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

transport : ∀ {u} {A B : Type u} → A ≡ B → A → B
transport P = coe01 (λ i → P i)

transport-refl : ∀ {u} {A : Type u} (x : A) → transport {A = A} refl x ≡ x
transport-refl {A} x i = coe0i (λ _ → A) (~ i) x

subst : ∀ {u v} {A : Type u} (P : A → Type v)
      → ∀ {x y} (q : x ≡ y) → P x → P y
subst P q = transport (ap P q)
{-# INLINE subst #-}

replace : ∀ {u v} {A : Type u} {P : A → Type v}
    → ∀ {x y} (q : x ≡ y) → P x → P y
replace {P} = subst P

rwt : ∀ {u v} {A : Type u} (P : A → Type v)
    → ∀ {x y} (q : x ≡ y) → P y → P x
rwt P p = replace (sym p)
{-# INLINE rwt #-}

-- subst2 : ∀ {u v w} {A : Type u} {B : Type v} (P : A → B → Type w)
--        → {w y : A} {x z : B} → w ≡ y → x ≡ z → P w x → P y z
-- subst2 {A} {B} P {w} {y} {x} {z} q s = subst (λ ((x , y) : A × B) → P x y) (ap2 _,_ q s)
-- J0 : ∀ {@0 u} {@0 A : Type u} {@0 x : A}
--   → (P : ∀ (@0 y) → @0 x ≡ y → Type v)
--   → P x (λ _ → x) → ∀ {@0 y} (@0 q : x ≡ y) → P y q
-- J0 {v} P c q = coe01 sq c
--   module J0 where
--     sq : I → Type v
--     sq i = P (q i) (λ j → q (i ∧ j))
-- {-# DISPLAY coe01 (J0.sq P q _) c = J0 P c q #-}


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
  path A p i j k = transp
    (λ l → A (ierp k (ierp l i j) j))
    (ierp k (ieq i j) i1)
    (p (ierp k i j))

J : ∀ {u v} {A : Type u} {x : A}
  → (P : ∀ y → x ≡ y → Type v)
  → P x refl → ∀ {y} (q : x ≡ y)
  → P y q
J  {v = v} {x = x} P c {y} q = transport (λ i → P (s i .fst) (s i .snd)) c
  where s = Singl-contr x .paths (y , q)
{-# INLINE J #-}

J-refl : ∀ {u v} {A : Type u} {x : A}
       → (P : ∀ y → x ≡ y → Type v)
       → (c : P x refl)
       → J P c refl ≡ c
J-refl {x} P = transport-refl
{-# INLINE J-refl #-}

transport⁻ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → B → A
transport⁻ P = coe01 (λ i → P (~ i))

transport⁻-transport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (b : B)
                       → transport p (transport⁻ p b) ≡ b
transport⁻-transport p b j = transp (λ i → p (j ∨ i)) j (transp (λ i → p (j ∨ ~ i)) j b)

transport-transport⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (a : A)
                     → transport⁻ p (transport p a) ≡ a
transport-transport⁻ p a = transport⁻-transport (sym p) a

-- transport-fiber-contr : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (b : B)
--                   → is-contr (Σ a ∶ A , transport p a ≡ b)
-- transport-fiber-contr p b .center = transport⁻ p b , transport⁻-transport p b
-- transport-fiber-contr {A = A} p b .paths (a , q) = goal where
--   base : transport⁻ p b ≡ a
--   base i = hcomp (∂ i) λ where
--     k (i = i0) → transport⁻ p b
--     k (i = i1) → transport-transport⁻ p a k
--     k (k = i0) → transport⁻ p (q (~ i))

--   fib : PathP (λ i → transport p (base i) ≡ b) (transport⁻-transport p b) q
--   fib i j = hcomp (∂ i ∨ ∂ j) λ where
--     k (i = i0) → {!!}
--     k (i = i1) → q (j ∧ k) -- q (j ∨ ~ k)
--     k (j = i0) → {!!}
--     k (j = i1) → q (~ i ∨ k) -- b
--     k (k = i0) → {!transport⁻ p (transport-filler (λ i → p i) a i)!}

--   goal : (transport⁻ p b , transport⁻-transport p b) ≡ (a , q)
--   goal i = base i , fib i

Path-over : ∀ {u} (A : I → Type u) → A i0 → A i1 → Type u
Path-over A x y = coe01 A x ≡ y

module Path-over {u} {A : I → Type u} {x} {y} where
  to-pathp : Path-over A x y → PathP A x y
  to-pathp p i = hcomp (∂ i) λ where
    j (i = i0) → x
    j (i = i1) → p j
    j (j = i0) → coe0i A i x

  from-pathp : PathP A x y → Path-over A x y
  from-pathp p i = coei1 A i (p i)

  eq-PathP : ∀ {ℓ} (P : I → Type ℓ) x y → PathP P x y ≡ Path-over P x y
  eq-PathP P x y i = PathP (∂.contract P i) (coe-filler P x i) y

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
is-prop→SquareP {B} bprop {a} p q r s i j =
  let base : (i j : I) → B i j
      base i j = coe01 (λ k → B (i ∧ k) (j ∧ k)) a
  in hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → bprop i0 j (base i0 j) (p j) k
    k (i = i1) → bprop i1 j (base i1 j) (r j) k
    k (j = i0) → bprop i i0 (base i i0) (q i) k
    k (j = i1) → bprop i i1 (base i i1) (s i) k
    k (k = i0) → base i j

SinglP-contr : ∀ {u} {A : I → Type u} (x : A i0)
             → is-contr (Σ y ∶ A i1 , PathP A x y)
SinglP-contr {A} x .center = coe01 A x , coe-filler A x
SinglP-contr {A} x .paths (y , q) i = _ , λ j → fill A (∂ i) j λ where
 j (i = i0) → coe0i A j x
 j (j = i0) → x
 j (i = i1) → q j

TotalP : ∀ {u v} {A : Type u} {B : A → Type v} {x}
       → (a : B x)
       → is-contr (Σ y ∶ A , Σ q ∶ (x ≡ y) , Σ b ∶ B y , PathP (λ i → B (q i)) a b)
TotalP {x} a .center = x , refl , a , refl
TotalP a .paths (y , q , b , α) i = q i , (λ j → q (i ∧ j)) , α i , λ j → α (i ∧ j)

loop-over : ∀ {u v} {A : Type u} (P : A → Type v)
          → {x y : A} (q : x ≡ y) (b : P y)
          → PathP (λ i → P ((sym q ∙ q) i)) b b
loop-over P q b i = hcomp (∂ i) λ where
  k (i = i0) → transport-refl b k
  k (k = i0) → transport (λ j → P (cat.invl q (~ j) i)) b
  k (i = i1) → transport-refl b k

sym-loop : ∀ {u v} {A : Type u} (P : A → Type v) {x y}
         → (q : x ≡ y) {a b : P y}
         → PathP (λ i → P (_∙_ (sym q) q i)) a b
         → a ≡ b
sym-loop P q {a} {b} α = transport (λ i → PathP (λ j → P (cat.invl q i j)) a b) α

is-prop→PathP-is-contr : ∀ {u} {A : I → Type u}
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

inhab-to-contr→is-prop : ∀ {u} {A : Type u} → (A → is-contr A) → is-prop A
inhab-to-contr→is-prop iprop x y = is-contr→is-prop (iprop x) x y

is-contr→is-set : ∀ {u} {A : Type u} → is-contr A → is-set A
is-contr→is-set c x y p q i j = outS do
  is-contr→extend c (∂ i ∨ ∂ j) λ where
    (i = i0) → p j
    (i = i1) → q j
    (j = i0) → x
    (j = i1) → y

is-contr→loop-is-refl : ∀ {u} {A : Type u} (c : is-contr A) → c .paths (c .center) ≡ refl
is-contr→loop-is-refl c = is-contr→is-set c _ _ (c .paths (c .center)) refl

is-contr→PathP : ∀ {u} {A : I → Type u}
               → ((i : I) → is-contr (A i))
               → (a0 : A i0) (a1 : A i1)
               → PathP A a0 a1
is-contr→PathP c = is-prop→PathP (λ i → is-contr→is-prop (c i))

is-prop→is-set : ∀ {u} {A : Type u} → is-prop A → is-set A
is-prop→is-set aprop x = is-contr→is-set (Contr x (aprop x)) x

is-prop-is-prop : ∀ {u} (A : Type u) → is-prop (is-prop A)
is-prop-is-prop A xprop yprop i x y = is-prop→is-set xprop x y (xprop x y) (yprop x y) i

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

IdsJ
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → is-identity-system R r
  → (P : ∀ b → R a b → Type ℓ'')
  → P a (r a)
  → ∀ {b} s → P b s
IdsJ ids P pr s =
  transport (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr

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

--Ids-concat :

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

-- contractible-system-contr : ∀ {u} {A : Type u} (R : A → A → Type u) → is-prop (Σ x ∶ A , is-contr (Σ y ∶ A , R x y))
-- contractible-system-contr R (c , α) (d , β) i = {!!} , {!!}
--   -- l0 : (γ : is-contr (Σ (R c))) → is-contr (Σ (R c))
--   -- l0 β = is-contr-is-prop (Σ (R c)) α β i

--   -- l1 : (γ : is-contr (Σ (R d))) → is-contr (Σ (R d))
--   -- l1 α = is-contr-is-prop (Σ (R d))  α

--   -- l1 : (γ : is-contr (Σ (R (β .fst)))) → ? ≡ ?
--   -- l1 = is-contr-is-prop (Σ (R (β .fst))) (β .snd) i

-- fiber-contr' : ∀ {u} {A : Type u} (x : A)
--              → is-contr (Σ f ∶ (A → A) , Σ R ∶ (A → A → Type u) , is-contr (Σ y ∶ A , R (f x) y))
-- fiber-contr' x .center = id , _≡_ , Singl-contr x
-- fiber-contr' x .paths (f , R , p) i = {!!} , {!!} , Contr ({!!} , {!!}) {!!}

-- contractible-system-contr : ∀ {u} {A : Type u} (x : A) → is-contr (Σ R ∶ (A → A → Type u) , is-contr (Σ y ∶ A , R x y))
-- contractible-system-contr x .center = _≡_ , Singl-contr x
-- contractible-system-contr x .paths (_~_ , U) i = {!!} , {!!} where
--   ids : is-identity-system _~_  λ a → {!U .fst .center .snd!}
--   ids = contr→identity-system {!!}
