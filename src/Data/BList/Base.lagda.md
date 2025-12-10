```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.BList.Base where

open import Lib.Type
open import Lib.Cubical.Base
open import Lib.Cubical.Kan
open import Lib.Equiv
open import Lib.Path
open import Lib.Sigma
open import Lib.Path.Gpd renaming (module cat to cat; cat to infixr 40 _∙_)
open import Lib.Path.Homotopy


-- private module _ where
--   private variable u v : Level ; A : Type u
--   infixr 20 _∷_
--   data SList {u} (A : Type u) : Type u where
--     [] : SList A
--     _∷_ : A → SList A → SList A
--     rw : ∀ x y zs → x ∷ zs ≡ y ∷ zs
    --ext : ∀ x y → ? ≡ braid ? ? ? ?
    -- ext : ∀ {ws x y} (f : (z : A) → z ∷ x ∷ ws ≡ z ∷ y ∷ ws) z
    --      → ap (z ∷_) (rw x y ws) ≡ braid (_∷ (x ∷ ws)) (_∷ (y ∷ ws)) f rfl
    --ext : ∀ x xs → xs ≡ x ∷ x ∷ xs
    --yank : ∀ x xs → Square (ext x xs) rfl (ext x xs) (twist x x xs) -- reidemeister move I


  -- test : ∀ x (ws : SList A) → ap (_∷_ x) (rw x x ws) ≡
  --                              braid (_∷ x ∷ ws) (_∷ x ∷ ws) (λ z _ → z ∷ x ∷ ws) rfl
  -- test x ws = ext (λ z → erfl (z ∷ x ∷ ws)) x


private variable u v : Level ; A : Type u

module test where
 infixr 18 _∷_
 data BList {u} (A : Type u) : Type u where
   [] : BList A
   _∷_ : A → BList A → BList A
   rw : ∀ y x zs → x ∷ zs ≡ y ∷ zs
   ext : ∀ x xs → x ∷ x ∷ xs ≡ xs
   rho : ∀ x y xs → Square (rw x y xs) rfl (rw x y xs) (rw x x xs)

 twist : ∀ x y (ws : BList A) → x ∷ y ∷ ws ≡ y ∷ x ∷ ws
 twist x y ws i = rw y x (rw x y ws i) i
 {-# DISPLAY rw x y (rw y x ws i) i = twist y x ws i #-}

 rw-refl : ∀ x (xs : BList A) → rw x x xs ≡ erfl (x ∷ xs)
 rw-refl x xs = loop-rfl (rw x x xs) (rw x x xs) (rho x x xs)

 inv : BList A → BList A
 inv [] = []
 inv (x ∷ xs) = x ∷ xs
 inv (rw y x xs i) = rw x y xs (~ i)
 inv (ext x [] i) = ext x [] i
 inv (ext x (z ∷ xs) i) = ext x (z ∷ xs) i
 inv (ext x (rw y z xs i) j) = ext x {!rw ? ? ? i!} j
 inv (ext x (ext x₁ xs i₁) i) = {!!}
 inv (ext x (rho x₁ y xs i₁ i₂) i) = {!!}
 inv (rho x y xs i j) = hcomp (∂ i ∨ ∂ j) λ where
   k (i = i0) → rw y x xs (~ j)
   k (i = i1) → rw y x xs (~ j)
   k (j = i0) → rw-refl y xs k (~ i)
   k (j = i1) → rw-refl x xs (~ k) (~ i)
   k (k = i0) → rho y x xs (~ i) (~ j)

 _++_ : BList A → BList A → BList A
 [] ++ ys = ys
 (x ∷ xs) ++ ys = x ∷ xs ++ ys
 rw y x xs i ++ ys = rw y x (xs ++ ys) i
 ext x xs i ++ ys = {!!}
 rho x y xs i j ++ ys = rho x y (xs ++ ys) i j

 cross : A → BList A → BList A
 cross a [] = a ∷ []
 cross a (x ∷ xs) = x ∷ a ∷ xs
 cross a (rw y x xs i) = rw y x (a ∷ xs) i
 cross a (ext x xs i) = {!!}
 cross a (rho x y xs i j) = rho x y (a ∷ xs) i j

 eqv : (a : A) → is-equiv (cross a)
 eqv a .is-equiv.contr [] .ctr = a ∷ [] , {!!}
 eqv a .is-equiv.contr (x ∷ []) .ctr = [] , {!!}
 eqv a .is-equiv.contr (x ∷ x₁ ∷ xs) .ctr = {!!}
 eqv a .is-equiv.contr (x ∷ rw y x₁ xs i) .ctr = {!!}
 eqv a .is-equiv.contr (x ∷ ext y xs i) .ctr = {!!}
 eqv a .is-equiv.contr (x ∷ rho x₁ y xs i i₁) .ctr = {!!}
 eqv a .is-equiv.contr (rw y x xs i) .ctr = {!!}
 eqv a .is-equiv.contr (ext x xs i) .ctr = {!!}
 eqv a .is-equiv.contr (rho x y xs i i₁) .ctr = {!!}
 eqv a .is-equiv.contr xs .paths = {!!}

 -- bswap : BList A → BList A
 -- bswap [] = []
 -- bswap (x ∷ xs) = cross x xs
 -- bswap (rw y x [] i) = rw y x [] i
 -- bswap (rw y x (z ∷ xs) i) = z ∷ rw y x xs i
 -- bswap (rw y x (rw z w xs i) j) = rw z w (rw y x xs j) i
 -- bswap (rw y x (rho w z xs i j) k) = rho w z (rw y x xs k) i j
 -- bswap (rho x y [] i j) = rho x y [] i j
 -- bswap (rho x y (z ∷ xs) i j) = z ∷ rho x y xs i j
 -- bswap (rho x y (rw z w xs i) j k) = rw z w (rho x y xs j k) i
 -- bswap (rho x y (rho w z xs i j) k l) = rho w z (rho x y xs k l) i j

 -- icross : A → BList A → BList A
 -- icross a = cross a ∘ inv

 -- -- gen : BList A → BList A
 -- -- gen = bswap ∘ bswap ∘ inv ∘ bswap

 -- interleave : A → A → BList A → BList A → BList A
 -- interleave a b [] bs = icross b bs
 -- interleave a b (x ∷ as) [] = cross a (x ∷ as)
 -- interleave a b (x ∷ as) (y ∷ bs) = cross a (x ∷ as) ++ icross b (y ∷ bs)
 -- interleave a b (x ∷ as) (rw y z bs i) = x ∷ (a ∷ (as ++ rw y z (b ∷ bs) i))
 -- interleave a b (x ∷ as) (rho z y bs i j) = x ∷ a ∷ (as ++ rho z y (b ∷ bs) i j)
 -- interleave a b (rw y x as i) [] = rw y x (a ∷ as) i
 -- interleave a b (rw y x as i) (z ∷ bs) = rw y x (a ∷ (as ++ (z ∷ b ∷ bs))) i
 -- interleave a b (rw y x as i) (rw z w bs j) = rw y x (a ∷ as ++ rw z w (b ∷ bs) j) i
 -- interleave a b (rw y x as i) (rho w z bs j k) = rw y x (a ∷ as ++ rho w z (b ∷ bs) j k) i
 -- interleave a b (rho x y as i j) [] = rho x y (a ∷ as) i j
 -- interleave a b (rho x y as i j) (z ∷ bs) = rho x y (a ∷ as ++ (z ∷ b ∷ bs)) i j
 -- interleave a b (rho x y as i j) (rw z w bs k) = rho x y (a ∷ as ++ rw z w (b ∷ bs) k) i j
 -- interleave a b (rho x y as i j) (rho w z bs k l) = rho x y (a ∷ as ++ rho w z (b ∷ bs) k l) i j

infixr 18 _∷_
data BList {u} (A : Type u) : Type u where
  [] : BList A
  _∷_ : A → BList A → BList A
  rw : ∀ y x zs → x ∷ zs ≡ y ∷ zs
  rho : ∀ x xs → Square (rw x x xs) rfl (rw x x xs) (rw x x xs)

syntax rw y x = y ▷ x

module category where
  open import Data.Acc
  _↝_ : ∀ {u} {A : Type u} → A → A → Type u
  _↝_ {u} {A} x y = ∀ ws → x ∷ ws ≡ y ∷ ws

twist : ∀ x y (ws : BList A) → x ∷ y ∷ ws ≡ y ∷ x ∷ ws
twist x y ws i = rw y x (rw x y ws i) i
{-# DISPLAY rw x y (rw y x ws i) i = twist y x ws i #-}



eqv : (x : A) → is-equiv (x ∷_)
eqv x .is-equiv.contr z .ctr .fst = z
eqv x .is-equiv.contr z .ctr .snd = {!cat.invl ?!}
eqv x .is-equiv.contr z .paths = {!!}




-- yang-baxter : ∀ x y z ws
--             → PathP (λ i → x ∷ y ∷ z ∷ ws ≡ z ∷ y ∷ x ∷ ws)
--                     (twist x y (z ∷ ws) ∙ twist x z (y ∷ ws) ∙ twist y z ws)
--                     (twist y z (x ∷ ws) ∙ twist x z (y ∷ ws) ∙ twist x y ws)
-- yang-baxter = ?

```
infixr 20 _∷_
data BList {u} (A : Type u) : Type u where
  [] : BList A
  _∷_ : A → BList A → BList A
  twist : ∀ x y zs → x ∷ y ∷ zs ≡ y ∷ x ∷ zs
  ext : ∀ x xs → xs ≡ x ∷ x ∷ xs
  rho : ∀ x xs → Square (ext x xs) rfl (ext x xs) (twist x x xs)

private variable u v : Level ; A : Type u

loop-rfl : ∀ {u} {A : Type u} {x y : A} (p : x ≡ y) (q : y ≡ y)
         → Square p rfl p q → q ≡ rfl
loop-rfl p q sq i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → conn p q j k
  k (i = i1) → p (j ∨ k)
  k (j = i0) → p k
  k (j = i1) → q (i ∨ k)
  k (k = i0) → sq i j

yank : ∀ x (xs : BList A) → twist x x xs ≡ erfl (x ∷ x ∷ xs)
yank x xs = loop-rfl (ext x xs) (twist x x xs) (rho x xs)

htpy→aut : {xs : BList A} (a b : A) → (∀ ws → a ∷ xs ≡ b ∷ ws) → BList A → BList A
htpy→aut a b h ws = h ws i1

alpha : ∀ x (xs ws : BList A) (p : x ∷ xs ≡ ws) → hsym (ext x xs) ≡ ap (x ∷_) p ∙ {!p!}
alpha ws = {!!}

cons-equiv : (a : A) → is-equiv (a ∷_)
cons-equiv a .is-equiv.contr ws .ctr .fst = a ∷ ws
cons-equiv a .is-equiv.contr ws .ctr .snd = hsym (ext a ws) 
cons-equiv a .is-equiv.contr ws .paths (xs , p) i .fst = {!!}
cons-equiv a .is-equiv.contr ws .paths (xs , p) i .snd = {!!} where
  c : fiber (a ∷_) ws
  c = a ∷ ws , hsym (ext a ws)

  d : fiber (a ∷_) ws
  d = xs , p

  t : a ∷ a ∷ ws ≡ a ∷ ws
  t = {!!}

  s : hsym (ext a ws) ≡ {!!}
  s = {!!}
