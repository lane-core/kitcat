```

{-# OPTIONS --safe --erased-cubical #-}

module Data.Vec where

open import Lib.Type

open import Agda.Builtin.List public
open import Lib.Nat
open import Lib.Interval
open import Lib.Kan
open import Lib.Path
open import Data.Nat

open import Lib.Data.Fin public
open ≤ℕ
open Path renaming (concat to infixl 40 _∙_)

length : ∀ {u} {A : Type u} → List A → Nat
length [] = 0
length (x ∷ xs) = S (length xs)

record Vec (n : Nat) {u} (A : Type u) : Type u where
  constructor vec
  field
    encoding : List A
    @0 pf : length encoding ≡ n

nil : ∀ {u} {A : Type u} → Vec 0 A
nil .Vec.encoding = []
nil .Vec.pf = λ (@0 i : _) → 0

_:-_ : ∀ {n u} {A : Type u} → Vec n A → A → Vec (S n) A
(xs :- x) .Vec.encoding = x ∷ Vec.encoding xs
(xs :- x) .Vec.pf = λ i → S (Vec.pf xs i)

data Vec-view {u} {A : Type u} : {n : Nat} → Vec n A → Type u where
  Nil : Vec-view nil
  Cons : ∀ {n xs} → Vec-view {n = n} xs → ∀ x → Vec-view (xs :- x)

module _ {u} {A : Type u} where
  length≡zero : {xs : List A} → @0 length xs ≡ Z → [] ≡ xs
  length≡zero {([])} p = refl
  length≡zero {x ∷ xs} p = ex-falso (pos-not-zero (length xs) p)

  nil-initial : (xs : Vec 0 A) → nil ≡ xs
  nil-initial (vec [] pf) i = vec [] (is-set-Nat Z Z refl pf i)
  nil-initial (vec (x ∷ xs) pf) = ex-falso (pos-not-zero (length xs) pf)

  Nil-hinitial : {xs : Vec 0 A} (As : Vec-view xs)
               → PathP (λ i → Vec-view (nil-initial xs i)) Nil As
  Nil-hinitial Nil i = Nil

  -- Nil-base  : {n : Nat} (xs : List A) (@0 pf : length xs ≡ 0) → Vec-view (vec xs pf)
  -- Nil-base [] pf = {!!}
  -- Nil-base (x ∷ xs) pf = {!!}

  Vec-elim : ∀ {v} (P : (n : Nat) → Vec n A → Type v)
           → {n : Nat} → (∀ (xs : Vec n A) x → P n xs → P (S n) (xs :- x))
           → P 0 nil → ∀ xs → P n xs
  Vec-elim P {n} s b xs = {!!} where
    elim : Vec-view xs → P n xs
    elim Nil = {!!}
    elim (Cons v x) = {!!}

  Cons-step : {n : Nat} {xs : Vec n A} (As : Vec-view xs)
            → {!!}
  Cons-step = {!!}

  cons : {n : Nat} (xs : List A) (@0 pf : length xs ≡ n)
       → Vec-view (vec xs pf)
  cons {(Z)} xs pf = {!!}
  cons {S n} xs pf = {!!}

  vec-view : ∀ {n u} {A : Type u} (xs : Vec n A) → Vec-view xs
  vec-view {(Z)} xs = {!!}
  vec-view {S n} xs = {!!}
