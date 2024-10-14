Lane Biocini
Ulf Norell (code taken from agda-prelude)
Oct 12th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Pi where

open import Lib.Prim

infix 3 Π
infix -1 Pi NatT

Π : ∀ {u v} {A : u type} (B : A → v type) → u ⊔ v type
Π {u} {v} {A} B = (x : A) → B x
{-# INLINE Π #-}

Pi : ∀ {u v} (A : u type) (B : A → v type) → u ⊔ v type
Pi A B = Π B
syntax Pi A (λ x → b) = Π x ꞉ A , b

NatT : ∀ {u v w} {ob : u type} → (ob → v type) → (ob → w type) → u ⊔ v ⊔ w type
NatT A B = ∀ x → A x → B x

syntax NatT A B = A ~> B

id : ∀ {u} {A : u type} → A → A
id = λ x → x
{-# INLINE id #-}

infixl -10 id
syntax id {A = A} x = x ofType A

const : ∀ {u v} {A : u type} {B : v type} → A → B → A
const x _ = x
{-# INLINE const #-}

flip : ∀ {u v w} {A : u type} {B : v type} {C : A → B → w type} → (∀ x y → C x y) → ∀ y x → C x y
flip f x y = f y x
{-# INLINE flip #-}

infixr 9 _∘_
_∘_ : ∀ {u v w} {A : u type} {B : A → v type} {C : ∀ x → B x → w type}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
(f ∘ g) x = f (g x)
{-# INLINE _∘_ #-}

infixr 9 _∘′_
_∘′_ : ∀ {u v w} {A : u type} {B : v type} {C : w type} →
         (B → C) → (A → B) → (A → C)
f ∘′ g = f ∘ g
{-# INLINE _∘′_ #-}

infixr -20 _$_ _$′_
infixr 0 case_of_ case_return_of_
_$_ : ∀ {u v} {A : u type} {B : A → v type} → (∀ x → B x) → ∀ x → B x
f $ x = f x

_$′_ : ∀ {u v}{A : u type} {B : v type} → (A → B) → A → B
f $′ x = f x

case_of_ : ∀ {u v} {A : u type} {B : v type} → A → (A → B) → B
case x of f = f x

case₂_,_of_ : ∀ {u v w} {A : u type} {B : v type} {C : w type} → A → B → (A → B → C) → C
case₂ x , y of f = f x y

case₃_,_,_of_ : ∀ {u v w z} {A : u type} {B : v type} {C : w type} {D : z type} → A → B → C → (A → B → C → D) → D
case₃ x , y , z of f = f x y z

case₄_,_,_,_of_ : ∀ {u v w z a} {A : u type} {B : v type} {C : w type} {D : z type} {E : a type} →
                A → B → C → D → (A → B → C → D → E) → E
case₄ x , y , z , w of f = f x y z w

case_return_of_ : ∀ {u v} {A : u type} (x : A) (B : A → v type) → (∀ x → B x) → B x
case x return B of f = f x

infixr 0 let-syntax
syntax let-syntax e (λ x → b) = let[ x := e ] b
let-syntax : ∀ {u v} {A : u type} {B : v type} → A → (A → B) → B
let-syntax x f = f x

{-# INLINE _$_ #-}
{-# INLINE _$′_ #-}
{-# INLINE case_of_ #-}
{-# INLINE case₂_,_of_ #-}
{-# INLINE case_return_of_ #-}

infixl 8 _on_
_on_ : ∀ {u v w} {A : u type} {B : A → v type} {C : ∀ x y → B x → B y → w type} →
         (∀ {x y} (z : B x) (w : B y) → C x y z w) → (f : ∀ x → B x) → ∀ x y →
         C x y (f x) (f y)
h on f = λ x y → h (f x) (f y)
{-# INLINE _on_ #-}

it : ∀ {u} {A : u type} {{x : A}} → A
it {{x}} = x
{-# INLINE it #-}

as-instance : ∀ {u v} {A : u type} {B : A → v type} (x : A) → (∀ {{x}} → B x) → B x
as-instance x f = f {{x}}
{-# INLINE as-instance #-}

record Instance {u} (A : u type) : u type where
  constructor !
  field {{x}} : A

mk-instance : ∀ {u} {A : u type} → A → Instance A
mk-instance x = ! {{x}}
{-# INLINE mk-instance #-}

-- Can be used to force normalisation at compile time.
static : ∀ {u} {A : u type} → A → A
static x = x
{-# STATIC static #-}
