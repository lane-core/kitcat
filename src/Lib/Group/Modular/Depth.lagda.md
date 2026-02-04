Depth function for the modular group PSL(2,Z).

The depth of an element measures its distance from the identity in the
Cayley graph, defined by mutual recursion on S-edges and R-edges.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Depth where

open import Core.Base using (_≡_; refl; ap)
open import Core.Type using (Type; 0ℓ)
open import Core.Data.Nat.Type using (Nat; Z)
  renaming (S to suc)

open import Lib.Group.Modular.Type
open import Lib.Group.Modular.Base
```


## Depth

Mutual recursion on S-edges and R-edges. Each `cross` or `step`
constructor adds one to the depth.

```agda
depth-η : S-edge → Nat
depth-θ : R-edge → Nat

depth-η e₀         = 0
depth-η e₁         = 1
depth-η (cross re) = suc (depth-θ re)

depth-θ (step _ se) = suc (depth-η se)

depth : PSL2Z → Nat
depth (η se) = depth-η se
depth (θ re) = depth-θ re
```


## Computational checks

All hold by definitional equality.

```agda
private
  depth-E   : depth E   ≡ 0; depth-E   = refl
  depth-S   : depth S   ≡ 1; depth-S   = refl
  depth-R   : depth R   ≡ 1; depth-R   = refl
  depth-R²  : depth R²  ≡ 1; depth-R²  = refl
  depth-SR  : depth SR  ≡ 2; depth-SR  = refl
  depth-SR² : depth SR² ≡ 2; depth-SR² = refl
  depth-RS  : depth RS  ≡ 2; depth-RS  = refl
  depth-R²S : depth R²S ≡ 2; depth-R²S = refl
```


## Interaction with generators

How depth relates to the generators s and r on the various forms.

The generator s on theta-forms adds one to depth; on cross-forms it
removes one. The generator r on eta-forms adds one; on theta-r+ it
preserves depth; on theta-r- it subtracts one.

```agda
depth-s-θ : (re : R-edge)
  → depth (s (θ re)) ≡ suc (depth-θ re)
depth-s-θ (r+ se) = refl
depth-s-θ (r- se) = refl

depth-r-η : (se : S-edge)
  → depth (r (η se)) ≡ suc (depth-η se)
depth-r-η e₀         = refl
depth-r-η e₁         = refl
depth-r-η (cross re) = refl

depth-r-θ-r+ : (se : S-edge)
  → depth (r (θ (r+ se))) ≡ suc (depth-η se)
depth-r-θ-r+ e₀         = refl
depth-r-θ-r+ e₁         = refl
depth-r-θ-r+ (cross re) = refl

depth-r-θ-r- : (se : S-edge)
  → depth (r (θ (r- se))) ≡ depth-η se
depth-r-θ-r- e₀         = refl
depth-r-θ-r- e₁         = refl
depth-r-θ-r- (cross re) = refl
```
