```

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Data.Fin where

open import Lib.Type
open import Lib.Nat
open IndOrd

-- module Fin where
--   record Fin (n : Nat) : Type where
--     constructor fin
--     field
--       ar : Nat
--       instance @0 pf : S ar ≤ n

--   open Fin public

--   zero : Fin 1
--   zero = fin Z (s≤s 0≤)

--   suc : ∀ {n} → Fin n → Fin (S n)
--   suc {(Z)} f = zero
--   suc {S n} (fin ar pf) .Fin.ar = S ar
--   suc {S n} (fin ar pf) .Fin.pf = s≤s pf

--   elim : ∀ {u} {A : Type u} → Fin 0 → A
--   elim (fin Z ())

-- open Fin using (Fin; zero; suc) hiding (module Fin) public
