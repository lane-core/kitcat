Lane Biocini
Ulf Norell (code taken from agda-prelude)
Oct 12th, 2024

```
{-# OPTIONS --safe #-}

module Lib.Pi.Cases where

infixr 0 case_of_ case_return_of_

open import Lib.Prim
open import Lib.Pi.Type

case_of_ : ∀ {u v} {A : u type} {B : v type} → A → (A → B) → B
case x of f = f x
{-# INLINE case_of_ #-}

case₂_,_of_ : ∀ {u v w} {A : u type} {B : v type} {C : w type} → A → B → (A → B → C) → C
case₂ x , y of f = f x y
{-# INLINE case₂_,_of_ #-}

case₃_,_,_of_ : ∀ {u v w z} {A : u type} {B : v type} {C : w type} {D : z type} → A → B → C → (A → B → C → D) → D
case₃ x , y , z of f = f x y z

case₄_,_,_,_of_ : ∀ {u v w z a} {A : u type} {B : v type} {C : w type} {D : z type} {E : a type} →
                A → B → C → D → (A → B → C → D → E) → E
case₄ x , y , z , w of f = f x y z w

case_return_of_ : ∀ {u v} {A : u type} (x : A) (B : A → v type) → (∀ x → B x) → B x
case x return B of f = f x
{-# INLINE case_return_of_ #-}
