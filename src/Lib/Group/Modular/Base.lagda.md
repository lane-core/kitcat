The generators s and r of the modular group, and derived operations.

The generator s is the involution and r is the order-3 rotation. These
are defined by pattern matching on the mutual inductive structure of
PSL2Z elements.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Group.Modular.Base where

open import Lib.Group.Modular.Type
open import Core.Type using (Type; 0ℓ)
```


## Generators

The involution s swaps the two base edges and toggles the crossing
structure. The rotation r steps clockwise, cycling through the three
R-edge positions.

```agda
s : PSL2Z → PSL2Z
s (η e₀)  = η e₁
s (η e₁)  = η e₀
s (s∙ re) = θ re
s (θ re)  = s∙ re

r : PSL2Z → PSL2Z
r (η e₀)   = r∙ e₀
r (η e₁)   = r∙ e₁
r (s∙ re)  = r∙ cross re
r (r∙ se)  = r²∙ se
r (r²∙ se) = η se
```


## Derived operations

Compositions of the generators, up to length 4.

```agda
r² sr rs : PSL2Z → PSL2Z
r² x = r (r x)
sr x = s (r x)
rs x = r (s x)

srs rsr r²s sr² : PSL2Z → PSL2Z
srs x = s (r (s x))
rsr x = r (s (r x))
r²s x = r (r (s x))
sr² x = s (r (r x))

sr²s rsr² r²sr r²sr² : PSL2Z → PSL2Z
sr²s x = s (r (r (s x)))
rsr² x = r (s (r (r x)))
r²sr x = r (r (s (r x)))
r²sr² x = r (r (s (r (r x))))
```
