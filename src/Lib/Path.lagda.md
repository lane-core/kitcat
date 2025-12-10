Lane Biocini
October 23, 2025

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Path where

open import Lib.Type
open import Lib.Base
open import Lib.Builtin
open import Lib.Underlying
open import Lib.Equal
open import Lib.Cubical.Base
open import Lib.Cubical.Kan hiding (fill)
open import Lib.Cut

private
  variable
    u v : Level
    A : I → Type u

Square : {A : I → Type u} {w x : A i0} {y z : A i1}
       → x ≡ w
       → x ≡ y :: A
       → y ≡ z
       → w ≡ z :: A
       → Type u
Square p q r s = PathP (∂.square _≡_ q s) p r
{-# DISPLAY PathP (∂.square _≡_ q s) p r = Square p q r s #-}

SquareP : (A : I → I → Type u)
        → {a00 : A i0 i0} {a01 : A i0 i1}
        → {a10 : A i1 i0} {a11 : A i1 i1}
        → PathP (λ j → A i0 j) a00 a01
        → PathP (λ i → A i i0) a00 a10
        → PathP (λ j → A i1 j) a10 a11
        → PathP (λ i → A i i1) a01 a11
        → Type u
SquareP A p q r s = PathP (λ i → PathP (λ j → A i j) (q i) (s i)) p r

idp : {A : Type u} {x : A} → x ≡ x
idp {x = x} = λ _ → x

dsym : {x : A i0} {y : A i1} → x ≡ y :: A → y ≡ x :: (λ i → A (~ i))
dsym q i = q (~ i)

module cat2 {u} {A : I → Type u} where
  sys : {w x : A i0} {y z : A i1}
      → x ≡ w → x ≡ y :: A → y ≡ z
      → (i : I) → Partials (∂ i) (λ _ → A i)
  sys p q r i = λ where
    j (i = i0) → p j
    j (j = i0) → q i
    j (i = i1) → r j

  cat2 : {w x : A i0} {y z : A i1}
      → x ≡ w → x ≡ y :: A → y ≡ z → w ≡ z :: A
  cat2 p q r i = hcomp (∂ i) (sys p q r i)

  fill : {w x : A i0} {y z : A i1}
       → (p : x ≡ w) (q : x ≡ y :: A) (r : y ≡ z)
       → SquareP (λ i _ → A i) p q r (cat2 p q r)
  fill p q r i j = hfill (∂ i) j (sys p q r i)

  refl-path : {x : A i0} {y : A i1} (p : x ≡ y :: A) → cat2 idp p idp ≡ p
  refl-path p i j = fill idp p idp j (~ i)

  is-composite : {w : A i0} {z : A i1} → w ≡ z :: A → A i0 → A i1 → Type u
  is-composite {w} {z} s x y = Σ p ∶ (x ≡ w)
                             , Σ q ∶ (x ≡ y :: A)
                             , Σ r ∶ (y ≡ z)
                             , Square p q r s

  record Path-composite {x : A i0} {z : A i1} (s : x ≡ z :: A) : Type u where
    field
      {a0} : A i0
      {a1} : A i1
      composite : is-composite s a0 a1

open cat2 using (cat2; Path-composite; is-composite) public

module cat where
  module _ {A : I → Type u} {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z) where
    sys : (i : I) → Partials (∂ i) (λ _ → A i)
    sys i k (i = i0) = x
    sys i k (k = i0) = p i
    sys i k (i = i1) = q k

    fun : x ≡ z :: A
    fun i = hcomp (∂ i) (sys i)

    fill : idp ≡ q :: ∂.square _≡_ p fun
    fill i j = hfill (∂ i) j (sys i)

  module _ {A : I → Type u} where
    cfill : {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (dsym p) idp q (fun p q)
    cfill {y} p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (j = i0) → y
      k (i = i0) → p (~ j)
      k (k = i0) → p (i ∨ ~ j)
      k (i = i1) → q (j ∧ k)

    bfill : {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ j)) p (fun p q) idp q
          -- p ≡ refl :: ∂.square _≡_ (p ∙ q) q
    bfill p q i j = hcomp (∂ i ∨ j) λ where
      k (i = i0) → p j
      k (i = i1) → q k
      k (j = i1) → q (i ∧ k)
      k (k = i0) → p (i ∨ j)

    rfill : {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (dsym p) q idp (fun p q)
          -- → dsym p ≡ erefl z :: ∂.square _≡_ q (p ∙ q)
    rfill {y} p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (j = i0) → q (i ∧ k)
      k (i = i0) → p (~ j)
      k (k = i0) → p (i ∨ ~ j)
      k (i = i1) → q k

  cone : {A : Type u} {x y z : A} (q : y ≡ z) (r : x ≡ z)
       → Square q (fun q (dsym r)) r (λ _ → z)
  cone q r i j = hcomp (∂ i ∨ j) λ where
    k (i = i0) → q (j ∧ k)
    k (i = i1) → r (j ∨ ~ k)
    k (j = i1) → q (i ∨ k)
    k (k = i0) → q i

  fan : {A : Type u} {x y z : A} (p : x ≡ y) (q : x ≡ z)
      → Square p (λ _ → x) q (fun (dsym p) q)
  fan {x} p q i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p j
    k (j = i0) → x
    k (i = i1) → q (j ∧ k)
    k (k = i0) → p (~ i ∧ j)

  lpush : {A : Type u} {w x y z : A}
        → (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
        → Square p q r s → Square (λ _ → x) q r (fun p s)
  lpush {x} p q r s sq i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → x
    k (j = i0) → q (i ∧ k)
    k (i = i1) → sq k j
    k (k = i0) → p (i ∧ j)

  rpush : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
        → Square p q r s → Square p (λ _ → x) (fun q r) s
  rpush {x} p q r s sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → x
    k (i = i0) → p (j ∧ k)
    k (j = i1) → sq i k
    k (k = i0) → q (i ∧ j)

  rpop : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
       → Square p (λ _ → x) (fun q r) s → Square p q r s
  rpop p q r s sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p j
    k (i = i1) → bfill q r j k
    k (j = i0) → q (i ∧ k)
    k (j = i1) → s i
    k (k = i0) → sq i j

hcat2 : {A : Type u} {x y z : A} {p q : x ≡ y} {r s : y ≡ z}
      → p ≡ q → r ≡ s → cat.fun p r ≡ cat.fun q s
hcat2 α β i = cat.fun (α i) (β i)

Path-type : Equality
Path-type .Equality._＝_ = _≡_
Path-type .Equality.refl {x} = λ _ → x
Path-type .Equality.sym p i = p (~ i)
Path-type .Equality.cat = cat.fun
Path-type .Equality.transport p = coe01 (λ i → p i)
Path-type .Equality.cong f p i = f (p i)
Path-type .Equality.Singl-contr (y , p) i = (p i) , λ j → p (i ∧ j)
Path-type .Equality.transport-path x P c i = coe0i (λ _ → P x (λ _ → x)) (~ i) c
Path-type .Equality.hcat = hcat2

open Equality (Path-type) public

{-# DISPLAY hcomp _ (cat.sys p q i) = cat p q i  #-}
{-# DISPLAY cat.fun = _∙_ #-}

infix 4 _≢_
_≢_ : {A : Type u} → A → A → Type u
x ≢ y = ¬ (x ≡ y)

J0 : ∀ {@0 u} {@0 A : Type u} {@0 x : A}
  → (P : ∀ (@0 y) → @0 x ≡ y → Type v)
  → P x (λ _ → x) → ∀ {@0 y} (@0 q : x ≡ y) → P y q
J0 {v} P c q = coe01 sq c
  module J0 where
    sq : I → Type v
    sq i = P (q i) (λ j → q (i ∧ j))
{-# DISPLAY coe01 (J0.sq P q _) c = J0 P c q #-}

tr : (Q : ∀ i → A i → Type v)
      → {x : A i0} {y : A i1} → PathP A x y
      → Q i0 x → Q i1 y
tr {v} Q q = coe01 square
  module subst where
    square : I → Type v
    square i = Q i (q i)

idtofun : ∀ {u} {A B : Type u} → A ≡ B → A → B
idtofun = subst (λ x → x)

ap : {@0 A : Type u} {@0 B : A → Type v} (f : ∀ x → B x)
  → {x y : A} (p : x ≡ y)
  → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

ap0 : {@0 A : Type u} {@0 B : A → Type v} (f : ∀ (@0 x) → B x)
    → {@0 x y : A} (@0 p : x ≡ y)
    → PathP (λ i → B (p i)) (f x) (f y)
ap0 f p i = f (p i)

apd : {A : I → Type u} {B : ∀ i → A i → Type v}
    → (f : ∀ i (a : A i) → B i a)
    → {x : A i0} {y : A i1} (p : PathP A x y)
    → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
apd f p i = f i (p i)

_∼_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → Π B → Π B → Type (u ⊔ v)
_∼_ f g = ∀ a → f a ≡ g a

funext : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i

funexti : ∀ {u} {@0 A : I → Type u} {@0 f g : (i : I) → A i}
        → ((i : I) → f i ≡ g i) → f ≡ g
funexti p i j = p j i

happly : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {@0 f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x

lhs : {A : Type u} {x y : A} (p : x ≡ y) → p ≡ refl :: ∂.square _≡_ p refl
lhs p i j = p (i ∨ j)
{-# INLINE lhs #-}

rhs : {A : Type u} {x y : A} (p : x ≡ y) → refl ≡ p :: ∂.square _≡_ refl p
rhs p i j = p (i ∧ j)
{-# INLINE rhs #-}

module _ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  {p : a00 ≡ a01} {q : a00 ≡ a10} {r : a10 ≡ a11} {s : a01 ≡ a11}
  where
  hflip : Square p q r s → Square r (dsym q) p (dsym s)
  hflip α i j = α (~ i) j
  {-# INLINE hflip #-}

  vflip : Square p q r s → Square (dsym p) s (dsym r) q
  vflip α i j = α i (~ j)
  {-# INLINE vflip #-}

  lrotate : Square p q r s → Square (dsym q) r (dsym s) p
  lrotate α i j = α (~ j) i
  {-# INLINE lrotate #-}

  rrotate : Square p q r s → Square s (dsym p) q (dsym r)
  rrotate α i j = α j (~ i)
  {-# INLINE rrotate #-}

  antitranspose : Square p q r s → Square (dsym r) (dsym s) (dsym p) (dsym q)
  antitranspose α i j = α (~ i) (~ j)
  {-# INLINE antitranspose #-}

  transpose : Square p q r s → Square q p s r
  transpose α i j = α j i
  {-# INLINE transpose #-}

  itranspose : Square p q r s → Square (dsym s) (dsym r) (dsym q) (dsym p)
  itranspose α i j = α (~ j) (~ i)
  {-# INLINE itranspose #-}

contractible : {A : Type u} → is-prop A → A → is-contr A
contractible p c .center = c
contractible p c .paths = p c

Composite : ∀ {u} {A : I → Type u} {w x : A i0} {y z : A i1}
            → (p : x ≡ w) (q : x ≡ y :: A) (r : y ≡ z) → Type u
Composite {A} {w} {z} p q r = Σ s ∶ PathP A w z , Square p q r s

module Composite {u} {A : I → Type u} {w x : A i0} {y z : A i1}
  (p : x ≡ w) (q : x ≡ y :: A) (r : y ≡ z)
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

```
Squares involving three variables have a degenerate face, hence
they are triangles up to homotopy. We can read transformations of
these degenerate squares as transporting the refl term along one of
the paths, so from reflexivity at x to y, or y to z, and so on.
```

module tri {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  (sq : Square (erefl x) p q r)
  where
  by-pre : Square (erefl y) (dsym p) r q
  by-pre i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ k)
    k (i = i1) → r j
    k (j = i0) → p (~ i ∧ k)
    k (j = i1) → q i
    k (k = i0) → sq j i
  {-# INLINE by-pre #-}

  by-comp : Square (erefl z) (dsym r) p (dsym q)
  by-comp i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → r (j ∨ k)
    k (i = i1) → p j
    k (j = i0) → r (~ i ∧ k)
    k (j = i1) → q (~ i)
    k (k = i0) → sq j (~ i)
  {-# INLINE by-comp #-}

Ext : ∀ {u} (A : I → Type u) (x : A i0) → Type u
Ext A x = Σ y ∶ A i1 , PathP A x y

qinvtofun : ∀ {u v} {A : Type u} {B : Type v} → Qinv A B → A → B
qinvtofun e = fst e
