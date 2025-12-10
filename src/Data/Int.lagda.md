Based on Tesla Zhang's "Two tricks to Trivialize Higher-Indexed Families" (2023)

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Int where

open import Lib.Type
open import Agda.Builtin.Int public
-- open import Lib.Cubical.Base
-- open import Lib.Nat
-- open import Lib.Bool
-- open import Lib.Plus
-- open import Lib.Sigma
-- open import Lib.Path
-- open import Lib.Path.Gpd
-- open import Data.Circle

private variable
  u : Level
  A : Type u

-- module Int where
--   data Helix (x : Circle) : Type where
--     zero : x ≡ base → Helix x
--     succ : ((i : I) → x ≡ loop i) → Helix x

--   open Helix public

--   Int : Type
--   Int = Helix base

  -- zero : Int
--   zero .spool = inl rfl

--   suc : Int → Int
--   suc (wind (inl x)) .spool = inl (cat loop x)
--   suc (wind (inr x)) .spool = inr λ i → cat loop (x i)

--   pred : Int → Int
--   pred (wind (inl x)) .spool = inl (cat (hsym loop) x)
--   pred (wind (inr x)) .spool = inr (λ i → cat (hsym loop) (x i))

--   neg : Int → Int
--   neg (wind (inl x)) .spool = inl (hsym x)
--   neg (wind (inr x)) .spool = inr λ i j → {!!}

--   add : Int → Int → Int
--   add p q .spool = {!!}



-- --   -- data View+ : Int → Type where
-- --   --   zz : View+ zero
-- --   --   ss : ∀ {x} → View+ x → View+ (suc x)

-- --   -- data View- : Int → Type where
-- --   --   n1 : View- (pred zero)
-- --   --   pp : ∀ {x} → View- x → View- (pred x)

-- --   -- data View (n : Int) : Type where
-- --   --   ps : View+ n → View n
-- --   --   ng : View- n → View n

-- --   -- view : (n : Int) → View n
-- --   -- view (wind p) = Circle-elim (λ x → View (wind x)) {!!} {!p!}

-- -- -- record Int : Type where
-- -- --   field
-- -- --     sgn : Bool
-- -- --     dist : Nat
-- -- --     @0 pf : sgn ≡ ff ⊎ dist ≢ 0
