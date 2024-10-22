Lane Biocini
Oct 10th, 2024

Credit to Ulf Norell's excellent [agda-prelude](https://github.com/UlfNorell/agda-prelude),
I decided to use his Dec module as a starting point for ours.

```
{-# OPTIONS --safe #-}

module Lib.Data.Dec where

open import Lib.Prim
open import Lib.Data.Empty
open import Lib.Trait.Uninhabited

infix 0 if-yes_then_else_ if-no_then_else_

data Dec {u} (P : u type) : u type where
 yes : P → Dec P
 no  : ¬ P → Dec P

if-yes_then_else_ : ∀ {u v} {A : u type} {B : v type} → Dec A → B → B → B
if-yes yes _ then x else _ = x
if-yes no  _ then _ else y = y

if-no_then_else_ : ∀ {u v} {A : u type} {B : v type} → Dec A → B → B → B
if-no d then x else y = if-yes d then y else x

Decided : ∀ {u} {P : u type} → Dec P → u type
Decided {P = P} (yes _) = P
Decided {P = P} (no  _) = ¬ P

decide : ∀ {u} {P : u type} (d : Dec P) → Decided d
decide (yes x) = x
decide (no x) = x
