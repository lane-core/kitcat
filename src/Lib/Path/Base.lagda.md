Lane Biocini
Oct 12th, 2024

Type definitions for our Path type

```

{-# OPTIONS --safe  #-}

module Lib.Path.Base where

open import Lib.Prim
open import Lib.Rel

open import Lib.Data.Fiber using (apc)
open import Lib.Path.Type public

tr : ∀ {u v} {A : u type} (B : A → v type) {x y : A} → x ≡ y → B x → B y
tr B = J (λ z _ → B z)

ap : ∀ {u v} {A : u type} {B : v type}
   → (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f = apc (λ x → x) f

module _ {u} {A : u type} where
 path-concat : rel.transitive (Id A)
 path-concat {x} f g = tr (x ≡_) g f

 path-inv : rel.symmetric (Id A)
 path-inv {x} f = tr (_≡ x) f refl
