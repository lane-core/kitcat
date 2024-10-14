Lane Biocini
Oct 12th, 2024

Type-class for uninhabited types

```

module Lib.Uninhabited where

open import Lib.Prim
open import Lib.Data.Empty

record Uninhabited {u} (A : u type) : u type where
 field
  void : A → ⊥

open Uninhabited ⦃ ... ⦄ public

module _ {u} {A : u type} where
 instance
  null : {{¬ A}} → Uninhabited A
  null {{na}} .void = na
