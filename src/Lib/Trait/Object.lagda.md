Lane Biocini
Oct 19th, 2024

Inspired by Elliot's "Felix.Object" module in his denotational design library

```

{-# OPTIONS --safe #-}

module Lib.Trait.Object where

open import Lib.Prim

record is-pair-type {u v} (_*_ : u type → v type → u ⊔ v type) : (u ⊔ v) ⁺ type
 where
 infixr 2 _×_

 field
  pr₁ : {A : u type} {B : v type} → A * B → A
  pr₂ : {A : u type} {B : v type} → A * B → B

 _×_ : u type → v type → u ⊔ v type
 _×_ = _*_

open is-pair-type ⦃ ... ⦄ public

{-# DISPLAY is-pair-type._×_ _ A B = A × B #-}

-- record Coproducts u v : (u ⊔ v) ⁺ type where
--  infixr 2 _⊎_
--  field
--   _⊎_ : u type → v type → u ⊔ v type
--   inj₁ : {A : u type} {B : v type} → A → A ⊎ B
--   inj₂ : {A : u type} {B : v type} → B → A ⊎ B

-- open Coproducts ⦃ ... ⦄ public
