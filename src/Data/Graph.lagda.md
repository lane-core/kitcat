Based on Tesla Zhang's "Two tricks to Trivialize Higher-Indexed Families" (2023)

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Graph where

open import Lib.Type
open import Lib.Nat

record Graph u v : Type₊ (u ⊔ v) where
  field
    o : Type u
    e : o → o → Type v

module Graph-closure {u v} (G : Graph u v) where
  private module G = Graph G

  data _↝̇_ : G.o → G.o → Type (u ⊔ v) where
    nil : ∀ x → x ↝̇ x
    snoc : ∀ {x y z} → x ↝̇ y → G.e y z → x ↝̇ z

  _↭_ : G.o → G.o → Type v
  x ↭ y = (G.e x y) ⊎ (G.e y x)

  _↭̇_ : G.o → G.o → Type (u ⊔ v)
  x ↭̇ y = (x ↝̇ y) ⊎ (y ↝̇ x)

  len : ∀ {x y} → x ↝̇ y → Nat
  len (nil x) = Z
  len (snoc p _) = S (len p)

  slen : ∀ {x y} → x ↭̇ y → Nat
  slen (inl p) = len p
  slen (inr p) = len p

  data _↝⁺_ : G.o → G.o → Type (u ⊔ v) where
    step : ∀ x y → x ↝⁺ y
    snoc : ∀ {x y z} → x ↝⁺ y → G.e y z → x ↝⁺ z
