Lane Biocini
Oct 16th, 2024

Finally getting around to this, your basic Maybe type

```

module Lib.Data.Maybe where

open import Lib.Prim

data Maybe {u} (A : u type) : u type where
  just : A → Maybe A
  nothing : Maybe A

{-# BUILTIN MAYBE Maybe #-}
