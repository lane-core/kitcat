```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.List where

open import Lib.Type
open import Lib.Api.Op.Bracket public

private variable
  u : Level
  A : Type u

module List where
  open import Agda.Builtin.List hiding (module List) public
  open import Lib.Nat
  open Agda.Builtin.List.List public

  len : [ A ] → Nat
  len [] = 0
  len (x ∷ xs) = S (len xs)

  cat : [ A ] → [ A ] → [ A ]
  cat [] bs = bs
  cat (x ∷ as) bs = x ∷ (cat as bs)


open List public using (List; []; _∷_)
