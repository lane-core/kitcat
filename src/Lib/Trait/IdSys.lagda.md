Lane Biocini
Oct 13th, 2024

From Rijke's Introduction to Homotopy Type Theory, but this construction is
heavily borrowed from Jon Sterling's implementation in the TypeTopology module
UF.IdentitySystem.

We also lean on 1lab's formalization of this concept, with some tweaks of course

```

{-# OPTIONS --safe #-}

module Lib.Trait.IdSys where

open import Lib.Trait.IdSys.Type public
open import Lib.Trait.IdSys.Dependent public
open import Lib.Trait.IdSys.Unbiased public
