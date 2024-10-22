Lane Biocini
Oct 9th, 2024

From Iosif Petrakis's paper [Univalent Typds](https://arxiv.org/abs/2205.06651v1)

```

{-# OPTIONS --safe #-}

module Lib.Trait.Typoid.Impl.Cut where

open import Lib.Prim
open import Lib.Rel.Base using (rel)
open import Lib.Rel.Over using (rel-over-rel)

open import Lib.Data.Sigma using (Σ; Sigma)

open import Lib.Trait.Cut
open import Lib.Trait.Setoid

open import Lib.Trait.Typoid.Type

 typoid-2cell-cut : ∀ {u v w} {ob : u type}
                  → ⦃ 𝓐 : is-typoid v w ob ⦄
                  → {x y : ob} {g h : is-typoid._≃_ 𝓐 x y}
                  → Cut (is-typoid._≃_ 𝓐 x y)
                     (λ f → is-typoid._≅_ 𝓐 f g)
                     (λ f _ → is-typoid._≅_ 𝓐 g h → is-typoid._≅_ 𝓐 f h)
 typoid-2cell-cut {u} {v} {w} {ob} {{A}} {x} {y} .seq =
  concat2 {x} {y}
  where open is-typoid A using (concat2)
