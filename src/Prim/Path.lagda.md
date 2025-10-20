```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Prim.Path where

open import Prim.Type
open import Prim.Data.Sigma

open import Prim.Interval
open import Prim.Kan hiding (fill)
open import Prim.Data.Nat using (Nat; Z; S)

open import Agda.Builtin.Cubical.Path public

private variable
  u v : Level
  @0 A : Type u
  @0 B : Type v
  P : I → Type u

Path : (A : Type u) → A → A → Type u
Path A = PathP (iconst A)

{-# DISPLAY PathP (iconst A) = Path A #-}

path-syntax : ∀ {u} (A : Type u) → A → A → Type u
path-syntax A = PathP (iconst A)
syntax path-syntax A x y = x ≡ y ∶ A

module Square {A : Type u} {@0 w x y z : A} (p : x ≡ y) (q : w ≡ z) where
  predicate : (i : I) → Type u
  predicate i = p i ≡ q i

Square : {A : Type u} {@0 w x y z : A} → x ≡ w → x ≡ y → y ≡ z → w ≡ z → Type u
Square p q r s = PathP (Square.predicate q s) p r
{-# DISPLAY PathP (Square.predicate q s) p r = Square p q r s #-}

module SquareP
  (A : I → I → Type u)
  {@0 a00 : A i0 i0} {@0 a01 : A i0 i1}
  {@0 a10 : A i1 i0} {@0 a11 : A i1 i1}
  (p : PathP (λ i → A i i0) a00 a10)
  (q : PathP (λ i → A i i1) a01 a11)
  where
  predicate : (i : I) → Type u
  predicate i = PathP (λ j → A i j) (p i) (q i)

SquareP : (A : I → I → Type u)
        → {@0 a00 : A i0 i0} {@0 a01 : A i0 i1}
        → {@0 a10 : A i1 i0} {@0 a11 : A i1 i1}
        → PathP (λ j → A i0 j) a00 a01
        → PathP (λ i → A i i0) a00 a10
        → PathP (λ j → A i1 j) a10 a11
        → PathP (λ i → A i i1) a01 a11
        → Type u
SquareP A p q r s = PathP (SquareP.predicate A q s) p r
{-# DISPLAY PathP (SquareP.predicate A q s) p r = SquareP A p q r s #-}

fiber : {A : Type u} {B : Type v} → (A → B) → B → Type (u ⊔ v)
fiber f y = Σ predicate
  module fiber where
    predicate = λ x → f x ≡ y
{-# DISPLAY Σ (fiber.predicate f y) = fiber f y #-}

J : {@0 x : A} (P : ∀ y → x ≡ y → Type v)
  → P x (λ i → x) → ∀ {y} (q : x ≡ y) → P y q
J P c q = coe01 (∂.square P q) c
{-# DISPLAY coe01 (∂.square P q) c = J P c q #-}

module J {u v} {A : Type u} {x : A} where
  refl : (P : ∀ y → x ≡ y → Type v) (c : P x (λ i → x))
       → c ≡ J P c (λ i → x)
  refl P = transport-filler (λ _ → P x (λ _ → x))

J#0 : {@0 x : A} (P : ∀ (@0 y) → @0 x ≡ y → Type v)
    → P x (λ _ → x) → ∀ {@0 y} (@0 q : x ≡ y) → P y q
J#0 P c q = coe01 (∂.square#0 P q) c
{-# DISPLAY coe01 (∂.square#0 P q) c = J#0 P c q #-}

refl : {x : A} → x ≡ x
refl {x} _ = x
{-# INLINE refl #-}

erefl : (x : A) → x ≡ x
erefl x _ = x
{-# INLINE erefl #-}

sym : ∀ {@0 x y} → PathP P x y → PathP (λ i → P (~ i)) y x
sym p i = p (~ i)
{-# INLINE sym #-}

actp : {@0 A : I → Type u} {B : (i : I) → (A i) → Type v}
     → (f : (i : I) (a : A i) → B i a)
     → {x : A i0} {y : A i1} (p : PathP A x y)
     → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
actp f p i = f i (p i)

ap : {@0 B : A → Type v} (f : ∀ x → B x) {@0 x y : A}
   → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

tr : (P : A → Type v) {@0 x y : A} (q : x ≡ y) → P x → P y
tr P q = coe01 (∂.line P q)
{-# DISPLAY coe01 (∂.line P q) = tr P q #-}

erased-tr : ∀ {u v} {@0 A : Type u} (P : @0 A → Type v)
   → {@0 x y : A} → @0 x ≡ y → P x → P y
erased-tr P q = ∂ i => P (q i)

idtofun : ∀ {u} {A B : Type u} → A ≡ B → A → B
idtofun = tr id
{-# DISPLAY tr id = idtofun #-}

{-# DISPLAY coe01 (∂.line P q) = tr P q #-}

lhs : {@0 x y : A} (p : x ≡ y) (i : I) → x ≡ p i
lhs p i j = p (i ∧ j)

rhs : {@0 x y : A} (p : x ≡ y) (i : I) → y ≡ p i
rhs p i j = p (i ∨ ~ j)

concat2 : {A : Type u} {@0 w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
concat2 {A} p q r = λ i → hc (iconst A) i (λ k → p (~ k)) (λ k → r k) q
  module concat2 where
    fill : Square (sym p) q r (concat2 p q r)
    fill i j = hc.fill (iconst A) i (λ k → p (~ k)) (λ k → r k) q j
--{-# DISPLAY hcomp _ (concat2.sys p q r i) = concat2 p q r i #-}

concat : ∀ {A : Type u} {x : A} {@0 y z} → x ≡ y → y ≡ z → x ≡ z
concat {x} p q = concat2 refl p q
  module concat where
    fill : Square refl p q (concat p q)
    fill i j = concat2.fill refl p q i j
{-# DISPLAY concat2 refl p q = concat p q #-}

lunit : {A : Type u} {x y : A} (p : x ≡ y) → p ≡ concat refl p
lunit {x} p i j = hcomp (∂ j ∨ ~ i) λ where
  k (j = i0) → x
  k (i = i0) → p (j ∧ k)
  k (j = i1) → p k
  k (k = i0) → x

runit : {A : Type u} {x y : A} (p : x ≡ y) → p ≡ concat p refl
runit p i j = concat.fill p refl j i

rinv : {A : Type u} {x y : A} (p : x ≡ y) → refl ≡ concat p (sym p)
rinv {x} p i j = hcomp (∂ j ∨ ~ i) λ where
  k (i = i0) → x
  k (j = i0) → x
  k (j = i1) → p (i ∧ ~ k)
  k (k = i0) → p (i ∧ j)

linv : {A : Type u} {x y : A} (p : x ≡ y) → refl ≡ concat (sym p) p
linv {y = y} p = rinv (sym p)

assoc : {A : Type u} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
      → concat p (concat q r) ≡ concat (concat p q) r
assoc {w} {z = z} p q r i j = hcomp (∂ j ∨ i) λ where
  k (j = i0) → w
  k (i = i1) → concat.fill (concat p q) r j k
  k (k = i0) → concat.fill p q j i
  k (j = i1) → hcomp (∂ k ∨ i) λ where
    l (i = i1) → r (k ∧ l)
    l (k = i0) → q i
    l (k = i1) → r l
    l (l = i0) → q (k ∨ i)


funext : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i

funexti : ∀ {u} {@0 A : I → Type u} {@0 f g : (i : I) → A i}
        → ((i : I) → f i ≡ g i) → f ≡ g
funexti p i j = p j i

happly : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {@0 f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x

record is-contr {u} (A : Type u) : Type u where
  field
    ctr : A
    paths : ∀ a → ctr ≡ a

open is-contr public

is-prop : Type u → Type u
is-prop A = (x y : A) → x ≡ y
  
is-set : Type u → Type u
is-set A = (x y : A) → is-prop (x ≡ y)

-- Alternative constructor for is-contr utilizing is-prop
contractible : is-prop A → A → is-contr A
contractible p c .ctr = c
contractible p c .paths = p c

is-hlevel : ∀ {ℓ} → Nat → Type ℓ → Type ℓ
is-hlevel (Z) A = is-contr A
is-hlevel (S Z) A = is-prop A
is-hlevel (S (S n)) A = (x y : A) → is-hlevel (S n) (x ≡ y)

record N-type ℓ n : Type₊ ℓ where
  no-eta-equality
  field
    ∣_∣ : Type ℓ
    #tr : is-hlevel n ∣_∣
