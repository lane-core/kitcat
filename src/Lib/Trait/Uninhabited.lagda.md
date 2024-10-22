Lane Biocini
Oct 12th, 2024

Type-class for uninhabited types

```

{-# OPTIONS --safe #-}

module Lib.Trait.Uninhabited where

infixl 8 ¬_

open import Lib.Prim
open import Lib.Data.Empty

record ¬_ {u} (A : u type) : u type where
 field
  void : A → 𝟘 {u}

open ¬_ ⦃ ... ⦄ public

instance
 -- nice
 empty-void : ∀ {u} → ¬ 𝟘 {u}
 empty-void .void ∅ = ∅
