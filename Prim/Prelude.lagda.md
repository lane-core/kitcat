Lane Biocini
Aug 26th, 2024

This is the Prelude file packaging all you need to have the equivalent
of MLTT-84, similar in philosophy to TypeTopology's Spartan MLTT library.
Our Base library includes this and lays on top of this the groundwork for
our Univalent mathematical inquiries.

This library is a model of the approach taken to each of the modules that
comprise Kitcat as a whole. We develop isolated modules that are then packaged
by a Prelude that structure the namespace as a whole for use in modules outside
of the namespace. Most of the functions live inside modules named after their
module imports, and only unique symbols are exported as public in the root level
of the module. The hope is that being able to use common names for analogous
operations across different types (segregated by a module prefix) leads to
having consistent naming conventions allowing you to work more efficiently in a
library with easy to memorize conventions.

From this package you'll get the MLTT base types as well as basic functors and
operations/induction principles related to them; also type families expressing
elementary predicates that will be important to us. You will not see lemmas here
however, these will be developed in the /Data modules.

```agda

{-# OPTIONS --safe #-}

module Prim.Prelude where

open import Prim.Universe public
open import Prim.Pi public

open import Global.Arrow public
open import Global.Cut public
open import Global.Underlying public

module sigma where
 open import Prim.Data.Sigma public
open sigma using (Σ; Sigma; _,_; _×_) public

module plus where
 open import Prim.Data.Plus public
open plus using (_⊎_; Plus; cases) public

module path where
 open import Prim.Data.Id public
open path using (Id; _≡_; refl; ap; tr) public

module empty where
 open import Prim.Data.Empty public
open empty using (𝟘; ⊥; ¬_; ex-falso) public

module unit where
 open import Prim.Data.Unit public
open unit using (𝟙; ⊤; ⋆) public

module nat where
 open import Prim.Data.Nat public
 module order where
  open import Prim.Data.Nat.Order public

open nat using (Nat; zero; suc) public

module bool where
 open import Prim.Data.Bool public
open bool using (Bool; tt; ff) public
