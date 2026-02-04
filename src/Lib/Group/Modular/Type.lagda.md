The modular group PSL(2,Z) as a mutual inductive type.

Adapted from TypeTopology, `Groups.ModularGroup.Type` (Todd Waugh Ambridge).
The modular group is the quotient of SL(2,Z) by its center {+I, -I}.
This module defines its elements via mutual inductive types representing
S-edges and R-edges in the Cayley graph, together with pattern synonyms
for common group words.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Type where

open import Core.Data.Sum using (_⊎_; inl; inr)
open import Core.Data.Bool using (Bool; true; false)
open import Core.Type using (Type; 0ℓ)
```


## Rotation sign

A rotation is either clockwise or counterclockwise.

```agda
R-sgn : Type 0ℓ
R-sgn = Bool

pattern cw  = false
pattern ccw = true
```


## Edges

The Cayley graph of PSL(2,Z) has two kinds of edges: S-edges
(involutions) and R-edges (order-3 rotations). These are mutually
defined because an S-edge can cross into an R-edge and vice versa.

```agda
data S-edge : Type 0ℓ
data R-edge : Type 0ℓ

data S-edge where
  e₀    : S-edge
  e₁    : S-edge
  cross : R-edge → S-edge

data R-edge where
  step : R-sgn → S-edge → R-edge
```


## The type

An element of PSL(2,Z) is either at an S-edge or an R-edge.

```agda
PSL2Z : Type 0ℓ
PSL2Z = S-edge ⊎ R-edge
```


## Pattern synonyms

Shorthand for common word forms in the generators s and r.

```agda
pattern η_ se = inl se
pattern θ_ re = inr re

pattern ρ i se = θ step i se
pattern σ i se = η cross (step i se)

pattern r+_ se = step cw se
pattern r-_ se = step ccw se

pattern s∙_ re   = η cross re
pattern r∙_ se   = ρ cw se
pattern r²∙_ se  = ρ ccw se

pattern sr∙_ se  = s∙ r+ se
pattern sr²∙_ se = s∙ r- se
pattern rs∙_ re  = r∙ cross re
pattern r²s∙_ re = r²∙ cross re
```


## Named elements

The first few words in s and r, up to length 4.

```agda
E S R R² : PSL2Z
E  = η e₀
S  = η e₁
R  = r∙ e₀
R² = r²∙ e₀

SR SR² RS R²S : PSL2Z
SR  = sr∙ e₀
SR² = sr²∙ e₀
RS  = r∙ e₁
R²S = r²∙ e₁

SRS SR²S RSR R²SR RSR² R²SR² : PSL2Z
SRS   = sr∙ e₁
SR²S  = sr²∙ e₁
RSR   = rs∙ r+ e₀
R²SR  = r²s∙ r+ e₀
RSR²  = rs∙ r- e₀
R²SR² = r²s∙ r- e₀
```
