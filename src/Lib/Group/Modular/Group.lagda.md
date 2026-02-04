The modular group PSL(2,Z) as a bundled group.

Assembles the multiplication, inverse, and axiom proofs from the
Modular submodules into a `Grp 0ℓ` record from `Lib.Group.Base`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Group where

open import Core.Base using (_≡_; refl)
open import Core.Type using (0ℓ)

open import Lib.Group.Base using (Grp)
open import Lib.Group.Modular.Type using (PSL2Z; E)
open import Lib.Group.Modular.Properties using (PSL2Z-is-set)
open import Lib.Group.Modular.Multiplication
  as M using (·-assoc; ·-E-right)
  renaming (_·_ to _*_)
open import Lib.Group.Modular.Inverse
  using (inv; ·-inv-left; ·-inv-right)
```


## The modular group

Left identity is definitional: `E * x` reduces to `x` because
`PSL2Z-gen-iter` on `E = η e₀` returns its first argument directly.

```agda
PSL2Z-Grp : Grp 0ℓ
PSL2Z-Grp .Grp.Carrier    = PSL2Z
PSL2Z-Grp .Grp._·_        = _*_
PSL2Z-Grp .Grp.e           = E
PSL2Z-Grp .Grp.inv         = inv
PSL2Z-Grp .Grp.assoc       = ·-assoc
PSL2Z-Grp .Grp.idl _       = refl
PSL2Z-Grp .Grp.idr         = ·-E-right
PSL2Z-Grp .Grp.invl        = ·-inv-left
PSL2Z-Grp .Grp.invr        = ·-inv-right
PSL2Z-Grp .Grp.has-is-set  = PSL2Z-is-set
```
