Lane Biocini
Oct 12th, 2024

Now we define higher homotopies for identity paths

```

{-# OPTIONS --safe #-}

module Lib.Path.HLevel where

open import Lib.Prim
open import Lib.Pi
open import Lib.Data.Sigma
open import Lib.Data.Nat
open import Lib.Path.Type

is-contr : ∀ {u} (A : u type) → u type
is-contr A = Σ c ꞉ A , ((x : A) → c ≡ x)

is-prop : ∀ {u} (A : u type) → u type
is-prop A = (x y : A) → x ≡ y

is-set : ∀ {u} (A : u type) → u type
is-set A = (x y : A) → is-prop (x ≡ y)

is-groupoid : ∀ {u} (A : u type) → u type
is-groupoid A = (x y : A) → is-set (x ≡ y)

is-hlevel : ∀ {u} → Nat → (A : u type) → u type
is-hlevel (zero) A = is-prop A
is-hlevel (suc n) A = (x y : A) → is-hlevel n (x ≡ y)
