```agda

{-# OPTIONS --safe --erased-cubical #-}

module HData.Q where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Kan
open import Lib.Equiv
open import Lib.Path
open import Lib.Sigma
open import Lib.Path.Gpd renaming (module cat to cat; cat to infixr 40 _∙_)
open import Lib.Path.Homotopy
open import Lib.Pointed

infixr 8 _∷_

data Q {u} (A : Type u) : Type u where
  base : Q A
  _∷_ : A → Q A → Q A
  ext : ∀ x xs → x ∷ xs ≡ x ∷ x ∷ xs
  rw : ∀ x y ws → x ∷ ws ≡ y ∷ ws
  rho : ∀ x xs → Square (ext x xs) (rw x x xs) (ext x xs) rfl

private variable u : Level ; A : Type


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
