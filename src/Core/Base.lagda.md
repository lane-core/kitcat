Core path types, fibers, h-level predicates, and interval operations.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Base where

open import Core.Type using (Level; Type; _⊔_; _₊; Typeω; 0ℓ; Irr)
open import Core.Data.Sigma

open import Agda.Primitive.Cubical public
  using ( IUniv   -- IUniv : SSet₁
        ; I       -- I : IUniv
        ; i0      -- i0 : I
        ; i1      -- i1 : I
        ; IsOne   -- IsOne : I → Typeω
        ; Partial -- Partial : ∀{ℓ} (i : I) (A : Type ℓ) → Type ℓ
                  -- Partial i A = IsOne i → A
        ; PartialP
        ; primPOr
        )
  renaming ( primIMin to _∧_ -- _∧_ : I → I → I
           ; primIMax to _∨_ -- _∨_ : I → I → I
           ; primINeg to ~_  -- ~_ : I → I
           ; itIsOne    to 1=1       -- 1=1 : IsOne i1
           ; isOneEmpty to is1-empty -- is1-empty : ∀ {ℓ} {A : Partial i0 (Type ℓ)}
                                     --           → PartialP i0 A
           ; IsOne1     to is1-left  -- is1-left  : ∀ i j → IsOne i → IsOne (i ∨ j)
           ; IsOne2     to is1-right -- is1-right : ∀ i j → IsOne j → IsOne (i ∨ j)
           )

-- Import the core primitives early?
-- import Agda.Builtin.Cubical.HCompU

ILevel : Type
ILevel = I → Level

IType : ∀ u → Type (u ₊)
IType u = I → Type u

iconst : ∀ {u} {@0 A : Type u} → A → I → A
iconst a _ = a
{-# INLINE iconst #-}

iflip : ∀ {u} {@0 A : I → I → Type u} → (∀ i j → A i j) → ∀ i j → A j i
iflip {A} f = λ j i → f i j
{-# INLINE iflip #-}

ieq : I → I → I
ieq i j = (i ∧ j) ∨ (~ i ∧ ~ j)

ierp : I → I → I → I
ierp t x y = (x ∧ ~ t) ∨ (y ∧ (t ∨ x))
{-# INLINE ierp #-}

imp : I → I → I
imp x y = ~ x ∨ y
{-# INLINE imp #-}

iota-notation : ∀ {u} {A : I → Type u} → (∀ i → A i) → (∀ i → A i)
iota-notation f = f
syntax iota-notation (λ i → b) = ι i , b

private
  variable
    ℓ : I → Level
    u : Level
    A : Type u

open import Agda.Builtin.Cubical.Path public
  renaming (_≡_ to infix 2 _≡_)

∂ : I → I
∂ i = ~ i ∨ i

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

_[_≡_] pathp-syntax : ∀ {u} (A : I → Type u) → A i0 → A i1 → Type u
_[_≡_] = PathP
pathp-syntax = PathP
{-# DISPLAY pathp-syntax = PathP #-}
syntax pathp-syntax A x y = x ≡ y ∶ A

infixl 70 ∂

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = _≡_

refl : ∀ {u} {A : Type u} {x : A} → x ≡ x
refl {x = x} = λ _ → x
{-# INLINE refl #-}

sym : ∀ {u} {A : I → Type u} {x : A i0} {y : A i1}
    → PathP A x y → PathP (λ i → A (~ i)) y x
sym p i = p (~ i)
{-# INLINE sym #-}

ap : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v}
   → (f : ∀ x → B x) {x y : A} (p : x ≡ y)
   → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)
{-# INLINE ap #-}

ap-era : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} (f : ∀ (@0 x) → B x)
    → {x y : A} (@0 p : x ≡ y)
    → PathP (λ i → B (p i)) (f x) (f y)
ap-era f p i = f (p i)
{-# INLINE ap-era #-}

apd : ∀ {u v} {@0 A : I → Type u} {@0 B : ∀ i → A i → Type v}
    → (f : ∀ i (a : A i) → B i a)
    → {x : A i0} {y : A i1} (p : PathP A x y)
    → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
apd f p i = f i (p i)
{-# INLINE apd #-}

ap2 : ∀ {u v w} {@0 A : Type u} {@0 B : A → Type v} {@0 C : ∀ x → B x → Type w}
  → (f : ∀ x a → C x a)
  → {x y : A} (p : x ≡ y)
  → {a : B x} {b : B y}
  → (q : PathP (λ i → B (p i)) a b)
  → PathP (λ i → C (p i) (q i)) (f x a) (f y b)
ap2 f p q i = f (p i) (q i)
{-# INLINE ap2 #-}

ap2s : ∀ {u v w} {@0 A : Type u} {@0 B : Type v} {@0 C : Type w}
    → (f : A → B → C)
    → {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ≡ a₂
    → b₁ ≡ b₂
    → f a₁ b₁ ≡ f a₂ b₂
ap2s f {a₁} {a₂} {b₁} {b₂} p q i = f (p i) (q i)
{-# INLINE ap2s #-}

fiber : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → B → Type (u ⊔ v)
fiber f y = Σ (λ x → f x ≡ y)

record is-contr {u} (A : Type u) : Type u where
  no-eta-equality
  constructor Contr
  field
    center : A
    paths : (y : A) → center ≡ y

open is-contr public
{-# INLINE Contr #-}

is-prop : ∀ {u} → Type u → Type u
is-prop A = (x y : A) → x ≡ y
{-# INLINE is-prop #-}

is-set : ∀ {u} → Type u → Type u
is-set A = (x y : A) → is-prop (x ≡ y)
{-# INLINE is-set #-}

Irr-is-prop : ∀ {u} {A : Type u} → is-prop (Irr A)
Irr-is-prop _ _ = refl

HCell : {A : I → Type u} {w x : A i0} {y z : A i1}
       → x ≡ w
       → x ≡ y ∶ A
       → y ≡ z
       → w ≡ z ∶ A
       → Type u
HCell p q r s = PathP (∂.square _≡_ q s) p r
{-# DISPLAY PathP (∂.square _≡_ q s) p r = HCell p q r s #-}

SquareP : (A : I → I → Type u)
        → {a00 : A i0 i0} {a01 : A i0 i1}
        → {a10 : A i1 i0} {a11 : A i1 i1}
        → PathP (λ j → A i0 j) a00 a01
        → PathP (λ i → A i i0) a00 a10
        → PathP (λ j → A i1 j) a10 a11
        → PathP (λ i → A i i1) a01 a11
        → Type u
SquareP A p q r s = PathP (λ i → PathP (λ j → A i j) (q i) (s i)) p r

Square : {A : Type u} {w x y z : A}
       → x ≡ w
       → x ≡ y
       → y ≡ z
       → w ≡ z
       → Type u
Square p q r s = PathP (∂.square _≡_ q s) p r

Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  → Type ℓ
Triangle p q r = Square refl p q r

_~ᵢ_ : ∀ {u} {A : I → Type u} → (∀ i → A i) → (∀ i → A i) → Type u
f ~ᵢ g = ∀ i → f i ≡ g i

_∘i_ : ∀ {u} {v : I → Level} {A : I → Type u} {B : ∀ i → A i → Type (v i)}
     → (g : ∀ i (a : A i) → B i a)
     → (f : ∀ i → A i)
     → ∀ i → B i (f i)
_∘i_ g f = λ i → g i (f i)
infixr 40 _∘i_

module _ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  {p : a00 ≡ a01} {q : a00 ≡ a10} {r : a10 ≡ a11} {s : a01 ≡ a11}
  where
  hflip : HCell p q r s → HCell r (sym q) p (sym s)
  hflip α i j = α (~ i) j
  {-# INLINE hflip #-}

  vflip : HCell p q r s → HCell (sym p) s (sym r) q
  vflip α i j = α i (~ j)
  {-# INLINE vflip #-}

  lrotate : HCell p q r s → HCell (sym q) r (sym s) p
  lrotate α i j = α (~ j) i
  {-# INLINE lrotate #-}

  rrotate : HCell p q r s → HCell s (sym p) q (sym r)
  rrotate α i j = α j (~ i)
  {-# INLINE rrotate #-}

  antitranspose : HCell p q r s → HCell (sym r) (sym s) (sym p) (sym q)
  antitranspose α i j = α (~ i) (~ j)
  {-# INLINE antitranspose #-}

  transpose : HCell p q r s → HCell q p s r
  transpose α i j = α j i
  {-# INLINE transpose #-}

  itranspose : HCell p q r s → HCell (sym s) (sym r) (sym q) (sym p)
  itranspose α i j = α (~ j) (~ i)
  {-# INLINE itranspose #-}


```

## Homotopy (Pointwise Path)

Homotopy between dependent functions, following Rijke §13.

```agda

_~_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → (f g : (x : A) → B x) → Type (u ⊔ v)
f ~ g = (x : _) → f x ≡ g x
infix 3 _~_

funext : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i
{-# INLINE funext #-}

funexti : ∀ {u} {@0 A : I → Type u} {f g : (i : I) → A i}
        → ((i : I) → f i ≡ g i) → f ≡ g
funexti p i j = p j i
{-# INLINE funexti #-}

happly : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} {f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x
{-# INLINE happly #-}

hrefl : ∀ {u v} {A : Type u} {B : A → Type v} {f : (x : A) → B x} → f ~ f
hrefl _ = refl
{-# INLINE hrefl #-}

```
