```agda

{-# OPTIONS --safe --erased-cubical #-}

module HData.Quandle where

open import Lib.Type
open import Lib.Builtin hiding (_∷_)
open import Lib.Cubical.Base
open import Lib.Cubical.Kan
open import Lib.Path
open import Lib.Equal renaming (cat to infixr 40 _∙_)

infixr 8 _∷_

private variable u : Level ; A : Type

data Q {u} (A : Type u) : Type u where
  base : Q A
  _∷_ : A → Q A → Q A
  inlp : ∀ x y xs → x ∷ xs ≡ x ∷ y ∷ xs
  inrp : ∀ x y xs → y ∷ xs ≡ x ∷ y ∷ xs
  yank : ∀ x → x ∷ x ∷ base ≡ base
  loop : ∀ x xs → inlp x x xs ≡ inrp x x xs

_ : ∀ (x y : A) xs → y ∷ x ∷ xs ≡ y ∷ x ∷ y ∷ xs
_ = λ x y xs → ap (y ∷_) (inlp x y xs)


```

ind : ∀ {v} (P : Q A → Type v)
    → (b : P base)
    → (s : ∀ x xs → P xs → P (x ∷ xs))
    → (l : ∀ x y ws (a : P ws) → PathP (λ i → P (inlp x y ws i)) (s x ws a) (s x (y ∷ ws) (s y ws a)))
    → (r : ∀ x y ws (a : P ws) → PathP (λ i → P (inrp x y ws i)) (s y ws a) (s x (y ∷ ws) (s y ws a)))
    → (ya : ∀ x (a : P (x ∷ base)) → PathP (λ i → P (yank x i)) (s x (x ∷ base) a) b)
    → (∀ x xs (a : P xs) → SquareP (λ i j → P (loop x xs i j)) (l x x xs a) rfl (r x x xs a) rfl)
    → ∀ ws → P ws
ind P b s l r yk lp base = b
ind P b s l r yk lp (x ∷ ws) = s x ws (ind P b s l r yk lp ws)
ind P b s l r yk lp (inlp x y ws i) = l x y ws (ind P b s l r yk lp ws) i
ind P b s l r yk lp (inrp x y ws i) = r x y ws (ind P b s l r yk lp ws) i
ind P b s l r yk lp (yank x i) = yk x (s x base b) i
ind P b s l r yk lp (loop x xs i j) = lp x xs (ind P b s l r yk lp xs) i j

extl : (x : A) → x ∷ base ≡ base
extl x = inlp x x base ∙ yank x

extr : (x : A) → x ∷ base ≡ base
extr x = inrp x x base ∙ yank x

idempl : ∀ (x : A) xs → x ∷ x ∷ xs ≡ x ∷ xs
idempl x ws = hsym (inlp x x ws)

idempr : ∀ (x : A) xs → x ∷ x ∷ xs ≡ x ∷ xs
idempr x ws = hsym (inrp x x ws)

map : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Q A → Q B
map f base = base
map f (x ∷ as) = f x ∷ map f as
map f (inlp x y as i) = inlp (f x) (f y) (map f as) i
map f (inrp x y as i) = inrp (f x) (f y) (map f as) i
map f (yank x i) = yank (f x) i
map f (loop x xs i j) = loop (f x) (map f xs) i j

map-id : ∀ {u} {A : Type u} (xs : Q A) → map (λ x → x) xs ≡ xs
map-id base = rfl
map-id (x ∷ xs) i = x ∷ map-id xs i
map-id (inlp x y xs i) j = inlp x y (map-id xs j) i
map-id (inrp x y xs i) j = inrp x y (map-id xs j) i
map-id (yank x i) j = yank x i
map-id (loop x xs i j) k = loop x (map-id xs k) i j

slidel : ∀ x y (ws : Q A) → x ∷ y ∷ y ∷ ws ≡ x ∷ x ∷ y ∷ ws
slidel x y ws = ap (x ∷_) (hsym (inlp y y ws)) ∙ inlp x x (y ∷ ws)

slider : ∀ x y (ws : Q A) → x ∷ y ∷ y ∷ ws ≡ x ∷ x ∷ y ∷ ws
slider x y ws = ap (x ∷_) (hsym (inrp y y ws)) ∙ inrp x x (y ∷ ws)

slidel-fill : ∀ x y (xs : Q A)
          → Square rfl (ap (x ∷_) (inlp y y xs)) (slidel x y xs) (inlp x x (y ∷ xs))
slidel-fill x y xs i j = cat.cfill (ap (x ∷_) (hsym (inlp y y xs))) (inlp x x (y ∷ xs)) j i

slider-fill : ∀ x y (xs : Q A)
          → Square rfl (ap (x ∷_) (inrp y y xs)) (slider x y xs) (inrp x x (y ∷ xs))
slider-fill x y xs i j = cat.cfill (ap (x ∷_) (hsym (inrp y y xs))) (inrp x x (y ∷ xs)) j i

rw : ∀ x y (xs : Q A) → x ∷ xs ≡ y ∷ xs
rw x y xs = inlp x y xs ∙ hsym (inrp x y xs)

rw-fill : ∀ x y (xs : Q A) → Square (hsym (inlp x y xs)) rfl (hsym (inrp x y xs)) (rw x y xs)
rw-fill x y xs i j = cat.cone (inlp x y xs) (inrp x y xs) i (~ j)

rho : ∀ (x : A) ws → PathP (λ i → loop x ws i (~ i) ≡ loop x ws i (~ i)) rfl (rw x x ws)
rho x ws i j = hcomp (∂ j ∨ ~ i) λ where
  k (i = i0) → inlp x x ws (j ∨ k)
  k (j = i0) → loop x ws i (~ i ∧ k)
  k (j = i1) → loop x ws i (~ i ∨ ~ k)
  k (k = i0) → inlp x x ws j

rw-refl : ∀ (x : A) ws → rw x x ws ≡ rfl
rw-refl x ws = loop-rfl (λ i → loop x ws i (~ i)) (rw x x ws) λ i j → rho x ws j i

chi : ∀ (x y : A) ws → Square (inlp x y ws) (rw x y ws) (inrp x y ws) rfl
chi x y ws = cat.cone (inlp x y ws) (inrp x y ws)

twist : ∀ (x y : A) xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
twist x y xs = hsym (inlp x y xs) ∙ inrp y x xs

cross : ∀ (x y : A) {xs ws} → y ∷ x ∷ xs ≡ ws → x ∷ y ∷ xs ≡ ws
cross x y {xs} {ws} = λ (p : y ∷ x ∷ xs ≡ ws) → cat2 (inlp x y xs) (inrp y x xs) p

uncross : ∀ (x y : A) {xs ws} → x ∷ y ∷ ws ≡ xs → xs ≡ y ∷ x ∷ ws
uncross x y {xs} {ws} = λ p → cat2 p (hsym (inlp x y ws)) (inrp y x ws)

alpha : ∀ x y z (ws : Q A) → y ∷ z ∷ ws ≡ z ∷ x ∷ y ∷ ws
alpha x y z ws = cross y z (inlp z x (y ∷ ws))

beta : ∀ x y z (ws : Q A) → x ∷ y ∷ ws ≡ z ∷ y ∷ x ∷ ws
beta x y z ws = cross x y (inrp z y (x ∷ ws))

lconj : ∀ x y z (ws : Q A) → x ∷ ws ≡ x ∷ y ∷ z ∷ ws
lconj x y z ws = inlp x y ws ∙ ap (x ∷_) (inlp y z ws)

conj : ∀ x y (xs : Q A) → ap (x ∷_) (inlp y x xs) ≡ beta x y x xs
conj x y xs = {!cross ? ?!}

inv : A → Q A → Q A
inv a base = a ∷ base
inv a (x ∷ xs) = x ∷ a ∷ xs
inv a (inlp x y xs i) = x ∷ inlp a y xs i
inv a (inrp x y xs i) = beta y a x xs i
inv a (loop x xs i j) = {!!}
inv a (yank x i) = hcomp (∂ i) λ where
  k (i = i0) → inrp x a (x ∷ base) k
  k (k = i0) → inlp a x (x ∷ base) i
  k (i = i1) → a ∷ yank x k

-- S : Q A → Q A
-- S base = base
-- S (x ∷ base) = x ∷ base
-- S (x ∷ y ∷ ws) = y ∷ x ∷ ws
-- S (x ∷ inlp y z ws i) = y ∷ inlp x z ws i
-- S (x ∷ inrp y z ws i) = {!!}
-- S (x ∷ yank x₁ i) = {!!}
-- S (inlp x y ws i) = {!!}
-- S (inrp x y ws i) = {!!}
-- S (yank x i) = {!!}


-- conj : ∀ (a : A) xs → a ∷ inv a xs ≡ xs
-- conj a base = yank a
-- conj a (x ∷ xs) = ap (a ∷_) (hsym (inlp x a xs)) ∙ hsym (inrp a x xs)
-- conj a (inlp x y xs i) j = {!!}
-- conj a (inrp x y xs i) = {!!}
-- conj a (yank x i) = {!!}

-- conj2 : ∀ (a : A) xs → inv a (a ∷ xs) ≡ xs
-- conj2 a base = yank a
-- conj2 a (x ∷ xs) = ap (a ∷_) (hsym (inrp a x xs)) ∙ hsym (inrp a x xs)
-- conj2 a (inlp x y xs i) = {!!}
-- conj2 a (inrp x y xs i) = {!!}
-- conj2 a (yank x i) = {!!}

-- qequiv : (a : A) → is-equiv (a ∷_)
-- qequiv a .is-equiv.contr ys .ctr .fst = inv a ys
-- qequiv a .is-equiv.contr ys .ctr .snd = conj a ys
-- qequiv a .is-equiv.contr ys .paths (xs , p) i = {!!}


_▷_ : A → Q A → Q A
A ▷ B = {!!}
S : Q A → Q A
S base = base
S (x ∷ base) = x ∷ base
S (x ∷ y ∷ ws) = y ∷ x ∷ ws
S (x ∷ rw y z ws i) = rw y z (x ∷ ws) i
S (x ∷ ext y ws i) = hcomp (∂ i) λ where
  k (i = i0) → y ∷ x ∷ ws
  k (k = i0) → ext y (x ∷ ws) i
  k (i = i1) → y ∷ rw y x (rw x y ws k) k
S (x ∷ rho y ws i j) = {!!}
S (ext x base i) = ext x base i
S (ext x (y ∷ ws) i) = hcomp (∂ i) λ where
  k (i = i0) → y ∷ x ∷ ws
  k (k = i0) → rw y x (rw x y ws i) i
  k (i = i1) → ext x (y ∷ ws) k
S (ext x (ext y ws i) j) = {!!}
S (ext x (rw x₁ y ws i₁) i) = {!!}
S (ext x (rho y ws i j) k) = {!!}
S (rw x y ws i) = {!!}
S (rho x xs i j) = {!!}

-- lem : ∀ a x y (ws zs : Q A) → x ∷ a ∷ ws ≡ y ∷ a ∷ zs → ws ≡ zs
-- lem a x y (z ∷ ws) (w ∷ zs) p = {!!} where
--   alpha = lem a x y ws zs {!!}
-- lem a x y (z ∷ ws) (ext x₁ zs i) p = {!!}
-- lem a x y (ext x₁ ws i) zs p = {!!}
-- qequiv : (a : A) → is-equiv (a ∷_)
-- qequiv a .is-equiv.contr (x ∷ ws) .ctr = ws , ?
-- qequiv a .is-equiv.contr (x ∷ ws) .paths (xs , p) i = α i , β i where
--   α : ws ≡ xs
--   α = {!!}

  -- β : Square (rw a x ws) (ap (a ∷_) α) p rfl
  -- β = {!!}




-- qequiv a .is-equiv.contr (ext x ws i) = {!!}
-- qequiv a .is-equiv.contr (rw x y ws i) = {!!}
