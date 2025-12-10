Lane Biocini
October 23, 2025

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Path.Homotopy where

open import Lib.Type
open import Lib.Cubical.Base
open import Lib.Cubical.Kan hiding (fill)
open import Lib.Path
open import Lib.Path.Gpd renaming (module cat to cat; cat to infixr 40 _∙_)
open import Lib.Sigma
open import Lib.Pointed

htcat : ∀ {u v} {A : Type u} {B : A → Type v}
     → {f g h : Π B} → f ∼ g → g ∼ h → f ∼ h
htcat α β = λ x → α x ∙ β x

icat : ∀ {u} {A : I → Type u} {f g h : ∀ i → A i}
     → (∀ i → f i ≡ g i)
     → (∀ i → g i ≡ h i)
     → (∀ i → f i ≡ h i)
icat α β = λ i → α i ∙ β i

ibraid : ∀ {u} {A : I → Type u}
       → (f g : ∀ i → A i) (q : ∀ i → f i ≡ g i)
       → q i0 ≡ q i1 :: (λ i → f i ≡ g i)
ibraid {A} f g q i j = q i j

braid : ∀ {u v} {A : Type u} {B : A → Type v}
      → (f g : Π B) (q : f ∼ g) {x0 x1 : A} (p : x0 ≡ x1)
      → PathP (λ i → B (p i)) (f x0) (g x1)
braid f g q p i = q (p i) i -- ibraid (λ i → f (p i)) (λ i → g (p i)) (λ i → q (p i)) i i

fbraid : ∀ {u v} {A : I → Type u} {B : ∀ i → A i → Type v}
       → (h : ∀ i (x : A i) → B i x)
       → (f g : ∀ i → A i) (q : ∀ i → f i ≡ g i)
       → h ∘ᵢ f ≡ h ∘ᵢ g :: λ j → ∀ i → B i (ibraid f g q i j)
fbraid h f g q i j = h j (q j i)

bcomp : ∀ {u v} {A : I → Type u} {B : ∀ i → A i → Type v}
       → (h : ∀ i (x : A i) → B i x)
       → (f g : ∀ i → A i) (q : ∀ i → f i ≡ g i)
       → ∀ i j → B i (ibraid f g q i j)
bcomp h f g q i j = h i (q i j)

dbraid : ∀ {u v} {A : I → Type u} {B : ∀ i → A i → Type v}
       → (h : ∀ i (x : A i) → B i x)
       → (f g : ∀ i → A i) (q : ∀ i → f i ≡ g i)
       → apd (λ i a → h i0 (q i0 i)) (q i0) ≡ apd (λ i a → h i1 (q i1 i)) (q i1)
       :: λ i → h i (f i) ≡ h i (g i)
       :: λ j → B i (ibraid f g q i j)
dbraid h f g q i j = h i (q i j)

depbraid : ∀ {u v w} {A : Type u} {B : A → Type v} {C : ∀ x → B x → Type w}
       → (h : ∀ x (y : B x) → C x y) (f g : Π B) (q : f ∼ g)
       → {x0 x1 : A} (p : x0 ≡ x1)
       → PathP (λ i → C (p i) (braid f g q p i)) (h x0 (f x0)) (h x1 (g x1))
depbraid {C} h f g q {x0} {x1} p i = fill i i where
  fill : apd (λ i a → h x0 (q x0 i)) p ≡ apd (λ i a → h x1 (q x1 i)) p
       :: λ i → h (p i) (f (p i)) ≡ h (p i) (g (p i))
       :: λ j → C (p i) (q (p i) j)
  fill i j = h (p i) (q (p i) j)

module braid where
  private variable
    u v w : Level
    A : Type u
    B : A → Type v
    C : ∀ a → B a → Type w

  fill : ∀ {u v} {A : Type u} {B : A → Type v}
       → (f g : Π B) (q : f ∼ g) {x0 x1 : A} (p : x0 ≡ x1)
       → Square (q x0) (ap f p) (q x1) (ap g p)
  fill f g q p i j = q (p i) j
  module fill where
    refl : (f g : Π B) (q : ∀ a → f a ≡ g a)
         → (x : A) → fill f g q (erfl x) ≡ erfl (q x)
    refl f g q = erfl ∘ erfl ∘ q

  refl : (f g : Π B) (q : f ∼ g) (x : A) → braid f g q (erfl x) ≡ q x
  refl f g q = erfl ∘ q

  id-nat : (f : Π B) {x y : A} (p : x ≡ y) → braid f f (erfl ∘ f) p ≡ ap f p
  id-nat f p = rfl

  dwhisker : {A : Type u} {B : A → Type v} {C : ∀ x → B x → Type v}
           → {f g : Π B}
           → (q : f ∼ g) (h : ∀ x (y : B x) → C x y)
           → {x y : A} (p : x ≡ y)
           → apd (λ i → h (p i)) (braid f g q p) ≡ depbraid h f g q p
  dwhisker q h p = rfl

  whisker : {B : Type v} {C : Type w} {f g : A → B}
          → (q : f ∼ g) (h : B → C)
          → {x y : A} (p : x ≡ y)
          → ap h (braid f g q p) ≡ braid (h ∘ f) (h ∘ g) (ap h ∘ q) p
  whisker q h p = rfl

  vcat : {f g h : Π B}
       → (q : f ∼ g) (r : g ∼ h)
       → {x y : A} (p : x ≡ y)
       → braid f h (htcat q r) p ≡ braid f g q p ∙ braid g h r (erfl y)
  vcat {f} {h} q r {x} {y} p =
    cat.unique (braid f h (λ a → q a ∙ r a) p) λ i j →
      hcomp (∂ i ∨ ~ j) λ where
        k (i = i0) → f x
        k (i = i1) → conn (q y) (r y) j k
        k (j = i0) → q (p i) (i ∧ k)
        k (k = i0) → q (p i) (i ∧ j)

  hcat : {A : Type u} {B : Type v} {f g : A → B} (q : f ∼ g)
       → {x y z : A} (p : x ≡ y) (p' : y ≡ z)
       → braid f g q (p ∙ p') ≡ ap f p ∙ braid f g q p'
  hcat {f} {g} q {x} {y} {z} p p' =
    cat.unique (braid f g q (p ∙ p')) λ i j →
      hcomp (∂ j ∨ ∂ i) λ where
        k (j = i0) → f (p i)
        k (j = i1) → q ((p ∙ p') i) (i ∨ ~ k)
        k (i = i0) → q x (j ∧ ~ k)
        k (i = i1) → q (p' j) j
        k (k = i0) → q (cat.fill p p' i j) j

  interchange : {A : Type u} {B : Type v} {f0 g0 f1 g1 : A → B}
              → (q0 : f0 ∼ g0) (q1 : f1 ∼ g1)
              → (r0 : f0 ∼ f1) (r1 : g0 ∼ g1)
              → {x y : A} (p : x ≡ y)
              → (∀ a → Square (q0 a) (r0 a) (q1 a) (r1 a))
              → braid f0 g1 (htcat q0 r1) p
              ≡ braid f0 f1 r0 p ∙ braid f1 g1 q1 (erfl y)
  interchange {f0} {f1} {g1} q0 q1 r0 r1 {x} {y} p sq =
    cat.unique (braid f0 g1 (htcat q0 r1) p) cut where
      cut : Square
        (erfl (f0 x))
        (braid f0 f1 r0 p)
        (braid f1 g1 q1 (erfl y))
        (braid f0 g1 (htcat q0 r1) p)
      cut = λ i j → hcomp (∂ j ∨ ∂ i) λ where
        k (i = i0) → q0 x (~ k)
        k (i = i1) → q1 (p (~ j ∨ k)) (j ∨ ~ k)
        k (j = i1) → cat.rfill (q0 (p (i ∧ k))) (r1 (p (i ∧ k))) i k
        k (k = i0) → r1 (p (i ∧ ~ j)) i
        k (j = i0) → sq (p i) i (~ k) where
        α : f0 x ≡ f1 y
        α i = r0 (p i) i
