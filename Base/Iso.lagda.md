```agda

{-# OPTIONS --safe #-}

module Base.Path.Inverse where

open import Prim.Universe

record Inverse {𝓊} (A : 𝓊 type) : 𝓤ω where

--module {𝓊} {𝓋} {A : 𝓊 type} {B : 𝓋 type} where

--record is-left-inverse (f : )
