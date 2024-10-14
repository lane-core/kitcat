Lane Biocini
Ulf Norell (copied from agda-prelude)
Oct 12th, 2024

```

module Lib.Erased where

open import Lib.Prim
open import Lib.Data.Empty

data [erased]-is-only-for-printing : Type where
  [erased] : [erased]-is-only-for-printing

private postulate erasedBottom : ⊥

{-# DISPLAY erasedBottom = [erased] #-}

erase-⊥ : ⊥ → ⊥
erase-⊥ _ = erasedBottom

erase-¬ : ∀ {u} {A : u type} → ¬ A → ¬ A
erase-¬ !a a = erase-⊥ (!a a)
