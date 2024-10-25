Lane Biocini
Oct 19th, 2024

```

{-# OPTIONS --safe #-}

module Lib.Trait.Setoid.Type where

open import Lib.Prim
open import Lib.Data.Sigma using (Σ; Sigma)

open import Lib.Rel.Base using (rel; reflexive; symmetric; transitive)
open import Lib.Rel.Over using (rel-over-rel)

open import Lib.Trait.Cut

record has-setoid {u v} {ob : u type} (path : rel v ob) : u ⊔ v ⁺ type
 where
 field
  eqv : reflexive path
  inv : symmetric path
  concat : transitive path

 instance
  setoid-cut : {y z : ob} → Cut ob (λ x → path x y) (λ x _ → path y z → path x z)
  setoid-cut .seq = concat

open has-setoid {{...}} renaming (inv to infixr 50 _⁻¹) using () public

setoid-over : ∀ {u v w} {ob : u type} (path : rel v ob)
                 → (pathp : rel-over-rel w path)
                 → u ⊔ v ⊔ w ⁺ type
setoid-over {u} {v} {w} {ob} path pathp = (x y : ob) → has-setoid (pathp {x} {y})

module setoid-over {u v w} {ob : u type} {path : rel v ob}
 {pathp : rel-over-rel w path}
 (pathp-eqv : setoid-over path pathp)
 where
 module _ {x y : ob} where
  open has-setoid (pathp-eqv x y)
   renaming (eqv to eqv2 ; inv to inv2; concat to concat2)
   public

record is-setoid {u} v (A : u type) : u ⊔ v ⁺ type
 where
 field
  _≃_ : A → A → v type
  has-st : has-setoid _≃_

 open has-setoid has-st public

Setoid : ∀ u v → (u ⊔ v) ⁺ type
Setoid u v = Σ ob ꞉ u type , is-setoid v ob

module Setoid {u v} (S : Setoid u v) where
 open Σ S

 ob : u type
 ob = fst

 open is-setoid snd public
