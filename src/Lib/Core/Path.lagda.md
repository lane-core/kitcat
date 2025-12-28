Lane Biocini
October 23, 2025

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Core.Path where

open import Lib.Core.Prim
open import Lib.Base
open import Lib.Core.Type
open import Lib.Core.Equal.Type
open import Lib.Core.Base
open import Lib.Core.Sub
open import Lib.Core.Kan hiding (fill)
open import Lib.Core.Transport

private
  variable
    u v : Level
    A : I → Type u

idp : {A : Type u} {x : A} → x ≡ x
idp {x = x} = λ _ → x

dsym : {x : A i0} {y : A i1} → x ≡ y ∶ A → y ≡ x ∶ (λ i → A (~ i))
dsym q i = q (~ i)

module cat2 {u} {A : I → Type u} where
  sys : {w x : A i0} {y z : A i1}
      → x ≡ w → x ≡ y ∶ A → y ≡ z
      → (i : I) → Partials (∂ i) (A i)
  sys p q r i = λ where
    j (i = i0) → p j
    j (j = i0) → q i
    j (i = i1) → r j

  cat2 : {w x : A i0} {y z : A i1}
      → x ≡ w → x ≡ y ∶ A → y ≡ z → w ≡ z ∶ A
  cat2 p q r i = hcomp (∂ i) (sys p q r i)

  fill : {w x : A i0} {y z : A i1}
       → (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z)
       → SquareP (λ i _ → A i) p q r (cat2 p q r)
  fill p q r i j = hfill (∂ i) j (sys p q r i)

  refl-path : {x : A i0} {y : A i1} (p : x ≡ y ∶ A) → cat2 idp p idp ≡ p
  refl-path p i j = fill idp p idp j (~ i)

open cat2 using (cat2) public

hcat2 : {A : Type u} {x y z : A} {p q : x ≡ y} {r s : y ≡ z}
      → p ≡ q → r ≡ s → cat.fun p r ≡ cat.fun q s
hcat2 α β i = cat.fun (α i) (β i)

cong2 : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
    → (f : A → B → C)
    → {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ≡ a₂
    → b₁ ≡ b₂
    → f a₁ b₁ ≡ f a₂ b₂
cong2 f {a₁} {a₂} {b₁} {b₂} p q = (ap (λ a → f a b₁) p) ∙ (ap (λ b → f a₂ b) q)

erefl : ∀ {u} {A : Type u} (x : A) → x ≡ x
erefl x = refl {x = x}

Singl : ∀ {u} {A : Type u} → A → Type u
Singl {A = A} x = Σ (λ a → (x ≡ a))
{-# INLINE Singl #-}

×-to-path : ∀ {u} {A : Type u} → {w x y z : A} → w ≡ y → x ≡ z → (w , x) ≡ (y , z)
×-to-path = cong2 _,_

Ω : ∀ {u} → Type* u → Type u
Ω (_ , a) = a ≡ a
{-# INLINE Ω #-}

Loop : ∀ {u} → Type* u → Type* u
Loop A .fst = Ω A
Loop A .snd = refl

record is-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    unit : (x : A) → inv (f x) ≡ x
    counit : (y : B) → f (inv y) ≡ y

Qinv : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Qinv A B = Σ (λ (f : A → B) → is-qinv f)
infix 6 Qinv

infix 4 _≢_
_≢_ : {A : Type u} → A → A → Type u
x ≢ y = ¬ (x ≡ y)

-- tr : (Q : ∀ i → A i → Type v)
--       → {x : A i0} {y : A i1} → PathP A x y
--       → Q i0 x → Q i1 y
-- tr {v} Q q = coe01 square
--   module subst where
--     square : I → Type v
--     square i = Q i (q i)

idtofun : ∀ {u} {A B : Type u} → A ≡ B → A → B
idtofun = subst (λ x → x)

ap0 : {@0 A : Type u} {@0 B : A → Type v} (f : ∀ (@0 x) → B x)
    → {@0 x y : A} (@0 p : x ≡ y)
    → PathP (λ i → B (p i)) (f x) (f y)
ap0 f p i = f (p i)

apd : {A : I → Type u} {B : ∀ i → A i → Type v}
    → (f : ∀ i (a : A i) → B i a)
    → {x : A i0} {y : A i1} (p : PathP A x y)
    → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
apd f p i = f i (p i)

funext : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i

funexti : ∀ {u} {@0 A : I → Type u} {@0 f g : (i : I) → A i}
        → ((i : I) → f i ≡ g i) → f ≡ g
funexti p i j = p j i

happly : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {@0 f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x

lhs : {A : Type u} {x y : A} (p : x ≡ y) → p ≡ refl ∶ ∂.square _≡_ p refl
lhs p i j = p (i ∨ j)
{-# INLINE lhs #-}

rhs : {A : Type u} {x y : A} (p : x ≡ y) → refl ≡ p ∶ ∂.square _≡_ refl p
rhs p i j = p (i ∧ j)
{-# INLINE rhs #-}

module Path {A : Type u} where
  open cat
  hsqueeze : {x y : A} {p q : x ≡ y} → p ∙ refl ≡ refl ∙ q → p ≡ q
  hsqueeze {p} {q} h = cat2 (unitr p) h (unitl q)

  vsqueeze : {x y : A} {p q : x ≡ y} → refl ∙ p ≡ q ∙ refl → p ≡ q
  vsqueeze {p} {q} h = cat2 (unitl p) h (unitr q)

  baxter : {w x y z : A}
         → (p : w ≡ x) (q : w ≡ y) (r : y ≡ z) (s : x ≡ z) (c : x ≡ y)
         → (H : Square p refl q c)
         → (K : Square s c r refl)
         → p ∙ s ≡ q ∙ r
  baxter {w} {x} {y} {z} p q r s c H K i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → w -- H i (~ k)
    k (i = i0) → fill p s j k -- fill p s j k
    k (j = i1) → K i k -- s (i ∨ k)
    k (k = i0) → H i j -- K i j

  lwhisker : {x y z : A} (p : x ≡ y) {q r : y ≡ z} → q ≡ r → p ∙ q ≡ p ∙ r
  lwhisker p = ap (p ∙_)

  rwhisker : {x y z : A} {p q : x ≡ y} (r : y ≡ z) → p ≡ q → p ∙ r ≡ q ∙ r
  rwhisker r = ap (_∙ r)

  loop-refl : {x y : A} (p : x ≡ y) (q : y ≡ y)
            → Square p refl p q → q ≡ refl
  loop-refl p q sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → conn p q j k
    k (i = i1) → p (j ∨ k)
    k (j = i0) → p k
    k (j = i1) → q (i ∨ k)
    k (k = i0) → sq i j

  commutes : {w x y z : A}
           → (p : w ≡ x) (q : x ≡ z) (r : w ≡ y) (s : y ≡ z)
           → Square p r s q → p ∙ q ≡ r ∙ s
  commutes {w} p q r s sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → p (~ i ∧ ~ k)
    k (j = i1) → s (~ i ∨ k)
    k (i = i0) → cat.rfill p q j k
    k (k = i0) → sq j (~ i)

Composite : ∀ {u} {A : I → Type u} {w x : A i0} {y z : A i1}
            → (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) → Type u
Composite {A} {w} {z} p q r = Σ s ∶ PathP A w z , Square p q r s

module Composite {u} {A : I → Type u} {w x : A i0} {y z : A i1}
  (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z)
  (α β : Composite p q r)
  where
  pr1 : α .fst ≡ β .fst
  pr1 i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → α .snd j k
    k (i = i1) → β .snd j k
    k (j = i0) → p k
    k (j = i1) → r k
    k (k = i0) → q j


  pr2 : PathP (λ i → Square p q r (pr1 i)) (α .snd) (β .snd)
  pr2 i j k = hcomp (∂ i ∨ ∂ j ∨ ~ k) λ where
    l (i = i0) → α .snd j (k ∧ l)
    l (i = i1) → β .snd j (k ∧ l)
    l (j = i0) → p (k ∧ l)
    l (j = i1) → r (k ∧ l)
    l (k = i0) → q j
    l (l = i0) → q j

  unique : α ≡ β
  unique i = pr1 i , pr2 i

Composite-contr : ∀ {u} {A : I → Type u} {w x : A i0} {y z : A i1}
                → (p : x ≡ w) (q : x ≡ y ∶ A) (r : y ≡ z) → is-contr (Composite p q r)
Composite-contr p q r .center = cat2 p q r , cat2.fill p q r
Composite-contr p q r .paths f1 = Composite.unique p q r (cat2 p q r , cat2.fill p q r) f1

path-idem : ∀ {u} {A : Type u} (x : A) → refl ∙ refl ≡ refl {x = x}
path-idem x i = Composite.unique (refl {x = x}) refl refl
  (refl ∙ refl , λ j k → cat.fill (refl {x = x}) refl j k) (refl , refl) i .fst

Ext : ∀ {u} (A : I → Type u) (x : A i0) → Type u
Ext A x = Σ y ∶ A i1 , PathP A x y

qinvtofun : ∀ {u v} {A : Type u} {B : Type v} → Qinv A B → A → B
qinvtofun e = fst e

```
I want to do my own spin on identity systems, but until then shamelessly copied
from the excellent 1lab
```
