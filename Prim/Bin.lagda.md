Lane Biocini
March 27st, 2024

```agda
{-# OPTIONS --safe #-}

module Prim.Bin where

open import Prim.Universe

data Bin : Type where
 root : Bin
 ll : Bin → Bin
 rr : Bin → Bin

record BinarySystem {𝓊} (BS : 𝓊 type) : 𝓤ω where
 field
  𝟎 : BS
  𝟏 : BS
  base : BS
  left : BS → BS
  right : BS → BS
  bin-ind : ∀ {𝓋} (P : BS → 𝓋 type)
          →  P base
          → ((b : BS) → P b → P (left b))
          → ((b : BS) → P b → P (right b))
          → (x : BS) → P x

 {-# INLINE 𝟎 #-}
 {-# INLINE 𝟏 #-}
 {-# INLINE base #-}
 {-# INLINE left #-}
 {-# INLINE right #-}
 {-# INLINE bin-ind #-}

open BinarySystem ⦃ ... ⦄ public
