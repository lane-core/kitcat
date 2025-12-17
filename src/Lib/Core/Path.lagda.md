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

private
  variable
    u v : Level
    A : I → Type u

Square : {A : I → Type u} {w x : A i0} {y z : A i1}
       → x ≡ w
       → x ≡ y ∶ A
       → y ≡ z
       → w ≡ z ∶ A
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

dsym : {x : A i0} {y : A i1} → x ≡ y ∶ A → y ≡ x ∶ (λ i → A (~ i))
dsym q i = q (~ i)

module cat2 {u} {A : I → Type u} where
  sys : {w x : A i0} {y z : A i1}
      → x ≡ w → x ≡ y ∶ A → y ≡ z
      → (i : I) → Partials (∂ i) (λ _ → A i)
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

module cat where
  module _ {A : I → Type u} {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z) where
    sys : (i : I) → Partials (∂ i) (λ _ → A i)
    sys i k (i = i0) = x
    sys i k (k = i0) = p i
    sys i k (i = i1) = q k

    fun : x ≡ z ∶ A
    fun i = hcomp (∂ i) (sys i)

    fill : idp ≡ q ∶ ∂.square _≡_ p fun
    fill i j = hfill (∂ i) j (sys i)

  module _ {A : I → Type u} where
    cfill : {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (dsym p) idp q (fun p q)
    cfill {y} p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (j = i0) → y
      k (i = i0) → p (~ j)
      k (k = i0) → p (i ∨ ~ j)
      k (i = i1) → q (j ∧ k)

    bfill : {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ j)) p (fun p q) idp q
          -- p ≡ refl ∶ ∂.square _≡_ (p ∙ q) q
    bfill p q i j = hcomp (∂ i ∨ j) λ where
      k (i = i0) → p j
      k (i = i1) → q k
      k (j = i1) → q (i ∧ k)
      k (k = i0) → p (i ∨ j)

    rfill : {x : A i0} {y z : A i1} (p : x ≡ y ∶ A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (dsym p) q idp (fun p q)
          -- → dsym p ≡ erefl z ∶ ∂.square _≡_ q (p ∙ q)
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
Path-type .Equality._∙_ = cat.fun
Path-type .Equality.transport p = coe01 (λ i → p i)
Path-type .Equality.cong f p i = f (p i)
Path-type .Equality.Singl-contr (y , p) i = (p i) , λ j → p (i ∧ j)
Path-type .Equality.transport-path x P c i = coe0i (λ _ → P x (λ _ → x)) (~ i) c
Path-type .Equality.hcat = hcat2
{-# INLINE Path-type #-}

private module Eql = Equality Path-type
open Eql public

{-# DISPLAY hcomp _ (cat.sys p q i) = (p ∙ q) i  #-}
{-# DISPLAY cat.fun = _∙_ #-}

cong2 : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
    → (f : A → B → C)
    → {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ＝ a₂
    → b₁ ＝ b₂
    → f a₁ b₁ ＝ f a₂ b₂
cong2 f {a₁} {a₂} {b₁} {b₂} p q = (cong (λ a → f a b₁) p) ∙ (cong (λ b → f a₂ b) q)

erefl : ∀ {u} {A : Type u} (x : A) → x ＝ x
erefl x = refl {x = x}

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = _＝_

Singl : ∀ {u} {A : Type u} → A → Type u
Singl {A = A} x = Σ (λ a → (x ＝ a))
{-# INLINE Singl #-}

subst : ∀ {u v} {A : Type u} (P : A → Type v)
      → ∀ {x y} (q : x ＝ y) → P x → P y
subst P q = transport (cong P q)
{-# INLINE subst #-}

replace : ∀ {u v} {A : Type u} {P : A → Type v}
    → ∀ {x y} (q : x ＝ y) → P x → P y
replace {P} = subst P

rwt : ∀ {u v} {A : Type u} (P : A → Type v)
    → ∀ {x y} (q : x ＝ y) → P y → P x
rwt P p = replace (sym p)
{-# INLINE rwt #-}

J : ∀ {u v} {A : Type u} {x : A}
  → (P : ∀ y → x ＝ y → Type v)
  → P x refl → ∀ {y} (q : x ＝ y)
  → P y q
J  {v = v} {x = x} P c {y} q = subst (λ (x , p) → P x p) (Singl-contr (y , q)) c
{-# INLINE J #-}

J-refl : ∀ {u v} {A : Type u} {x : A}
       → (P : ∀ y → x ＝ y → Type v)
       → (c : P x refl)
       → J P c refl ＝ c
J-refl {x} = transport-path x
{-# INLINE J-refl #-}

×-to-path : ∀ {u} {A : Type u} → {w x y z : A} → w ＝ y → x ＝ z → (w , x) ＝ (y , z)
×-to-path = cong2 _,_

subst2 : ∀ {u v w} {A : Type u} {B : Type v} (P : A → B → Type w)
       → {w y : A} {x z : B} → w ＝ y → x ＝ z → P w x → P y z
subst2 {A} {B} P {w} {y} {x} {z} q s = subst (λ ((x , y) : A × B) → P x y) (cong2 _,_ q s)

Ω : ∀ {u} → Type* u → Type u
Ω (_ , a) = a ＝ a
{-# INLINE Ω #-}

Loop : ∀ {u} → Type* u → Type* u
Loop A .fst = Ω A
Loop A .snd = refl

record is-contr {u} (A : Type u) : Type u where
  constructor contr
  field
    center : A
    paths : (y : A) → center ＝ y

open is-contr public
{-# INLINE contr #-}

is-prop : ∀ {u} → Type u → Type u
is-prop A = (x y : A) → x ＝ y
{-# INLINE is-prop #-}

is-set : ∀ {u} → Type u → Type u
is-set A = (x y : A) → is-prop (x ＝ y)
{-# INLINE is-set #-}

is-groupoid : ∀ {u} → Type u → Type u
is-groupoid A = (x y : A) → is-set (x ＝ y)
{-# INLINE is-groupoid #-}

is-hlevel : ∀ {u} → Nat → Type u → Type u
is-hlevel Z A = is-contr A
is-hlevel (S Z) A = is-prop A
is-hlevel (S (S n)) A = ∀ x y → is-hlevel n (Path A x y)
{-# INLINE is-hlevel #-}

record is-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    unit : (x : A) → inv (f x) ＝ x
    counit : (y : B) → f (inv y) ＝ y

Qinv : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Qinv A B = Σ (λ (f : A → B) → is-qinv f)
infix 6 Qinv

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    unit : (x : A) → inv (f x) ＝ x
    counit : (y : B) → f (inv y) ＝ y
    adj : (x : A) → cong f (unit x) ＝ counit (f x)

_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
_≃_ A B = Σ (λ (f : A → B) → is-equiv f)
infix 6 _≃_

fiber : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → B → Type (u ⊔ v)
fiber f y = Σ (λ x → f x ＝ y)


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

lhs : {A : Type u} {x y : A} (p : x ≡ y) → p ≡ refl ∶ ∂.square _≡_ p refl
lhs p i j = p (i ∨ j)
{-# INLINE lhs #-}

rhs : {A : Type u} {x y : A} (p : x ≡ y) → refl ≡ p ∶ ∂.square _≡_ refl p
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

hconn : {A : I → Type u} {x y : A i0} {z : A i1}
     → (p : x ≡ y) (q : y ≡ z ∶ A)
     → SquareP (λ i j → A (i ∧ j)) p p q q
hconn {A} {y} {z} p q i j = hcomp (∂ i ∨ ∂ j) sys
  module hconn where
    sys : Partials (∂ i ∨ ∂ j) (λ _ → A (i ∧ j))
    sys k (k = i0) = q (i ∧ j)
    sys k (i = i0) = p (j ∨ ~ k)
    sys k (j = i0) = p (i ∨ ~ k)
    sys k (j = i1) = q i
    sys k (i = i1) = q j
{-# DISPLAY hcomp _ (hconn.sys p q i j) = hconn p q i j #-}

conn : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Square p p q q
conn = hconn

module Path {A : Type u} where
  open cat
  unitl : {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
  unitl p i j = rfill refl p j (~ i)

  unitr : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  unitr p i j = fill p refl j (~ i)

  invl : {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
  invl {x} {y} p i j = hcomp (∂ j ∨ i) λ where
        k (j = i0) → y
        k (k = i0) → p (~ j)
        k (j = i1) → p k
        k (i = i1) → p (~ j ∨ k)

  invr : {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
  invr p = invl (sym p)

  assoc : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
        → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  assoc {y} p q r k = transpose (fill p q) k ∙ transpose (rfill q r) (~ k)

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

path-idem : ∀ {u} {A : Type u} (x : A) → refl ∙ refl ＝ refl {x = x}
path-idem x i = Composite.unique (refl {x = x}) refl refl
  (refl ∙ refl , λ j k → cat.fill (refl {x = x}) refl j k) (refl , refl) i .fst

```
Squares involving three variables have a degenerate face, hence
they are triangles up to homotopy. We can read transformations of
these degenerate squares as transporting the refl term along one of
the paths, so from reflexivity at x to y, or y to z, and so on, so
we define "pre" and "post" operations to implement this.
```

Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  → Type ℓ
Triangle p q r = Square refl p q r

module Triangle {ℓ} {A : Type ℓ} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  (sq : Triangle p q r)
  where
  pre : Triangle (dsym p) r q
  pre i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ k)
    k (i = i1) → r j
    k (j = i0) → p (~ i ∧ k)
    k (j = i1) → q i
    k (k = i0) → sq j i
  {-# INLINE pre #-}

  post : Triangle (dsym r) p (dsym q)
  post i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → r (j ∨ k)
    k (i = i1) → p j
    k (j = i0) → r (~ i ∧ k)
    k (j = i1) → q (~ i)
    k (k = i0) → sq j (~ i)
  {-# INLINE post #-}

Ext : ∀ {u} (A : I → Type u) (x : A i0) → Type u
Ext A x = Σ y ∶ A i1 , PathP A x y

qinvtofun : ∀ {u v} {A : Type u} {B : Type v} → Qinv A B → A → B
qinvtofun e = fst e
