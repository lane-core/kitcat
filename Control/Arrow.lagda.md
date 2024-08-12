Lane Biocini
Jun 30, 2024

```
{-# OPTIONS --safe #-}

module Control.Arrow where

open import Prim.Universe

record Arrow {𝓊 𝓋 𝓌} {A : 𝓊 type} {B : 𝓋 type} (arr : 𝓌 type) : 𝓊 ⊔ 𝓋 ⊔ 𝓌 type where
 no-eta-equality
 field
  src : arr → A
  tgt : arr → B

 arrow : {p : arr} → A → B → 𝓌 type
 arrow {p} a b = arr

open Arrow ⦃ ... ⦄ public
{-# DISPLAY Arrow.src _ = src #-}
{-# DISPLAY Arrow.tgt _ = tgt #-}

module _ {𝓊} {𝓋} {A : 𝓊 type} {B : 𝓋 type} where
 instance
  arrow-λ : Arrow (A → B)
  arrow-λ .src = λ _ → A
  arrow-λ .tgt = λ _ → B

module _ {𝓊} {𝓋} {A : 𝓊 type} {B : A → 𝓋 type} {x : A} where
 instance
  arrow-Π : Arrow ((x : A) → B x)
  arrow-Π .src = λ _ → x
  arrow-Π .tgt = λ arr → arr x
