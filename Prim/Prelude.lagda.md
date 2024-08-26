Lane Biocini
Aug 26th, 2024

```agda

{-# OPTIONS --safe #-}

module Prim.Prelude where

open import Prim.Universe public
open import Prim.Pi public

open import Global.Arrow public
open import Global.Cut public
open import Global.Underlying public

module sigma where
 open import Prim.Sigma public
open sigma using (Σ; Sigma; _,_; _×_) public

module plus where
 open import Prim.Plus public
open plus using (_⊎_; Plus; cases) public

module path where
 open import Prim.Id public
open path using (Id; _≡_; refl; ap; tr) public

module empty where
 open import Prim.Empty public
open empty using (𝟘; ⊥; ¬_; ex-falso) public

module unit where
 open import Prim.Unit public
open unit using (𝟙; ⊤; ⋆) public

module bool where
 open import Prim.Bool public
open bool using (Bool; tt; ff) public

module dec where
 open import Prim.Dec public
open dec using (Dec; yes; no) public

module nat where
 open import Prim.Nat  public
open nat using (Nat; zero; suc) public
