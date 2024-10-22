Lane Biocini
Oct 5th, 2024

Definitions for relations

```
{-# OPTIONS --safe #-}

module Lib.Rel.Base where

open import Lib.Prim
open import Lib.Data.Sigma

rel : ∀ {u} v → u type → u ⊔ v ⁺ type
rel v ob = ob → ob → v type

module _ {u v} {ob : u type}
 (_~_ : rel v ob)
 where
 reflexive composition transitive symmetric : u ⊔ v type
 reflexive = (x : ob) → x ~ x
 composition = {x y z : ob} → y ~ z → x ~ y → x ~ z
 transitive = {x y z : ob} → x ~ y → y ~ z → x ~ z
 symmetric = {x y : ob} → x ~ y → y ~ x

-- In our library, we use all lowercase rel for homogenous relations,
-- capitalized Rel for heterogenous, and Mor (for "morphism") for
-- dependent relations, the latter notation of which is consistent
-- with the categorical interpretation of dependent types
Rel : ∀ {u v} w → u type → v type → u ⊔ v ⊔ w ⁺ type
Rel w A B = A → B → w type

Mor : ∀ {u v} w {A : u type} (B : A → v type) → u ⊔ v ⊔ w ⁺ type
Mor w {total} base = (x : total) → base x → w type
