Examples of W-type encodings: natural numbers and lists.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Data.W.Properties where

open import Core.Type
open import Core.Data.Bool
open import Core.Data.Empty
open import Core.Data.Maybe

open import Data.W.Type
open import Data.W.Base

```

## Natural numbers as a W-type

Natural numbers can be encoded as W Bool Nat-arity where:
- true maps to the empty type (zero has no predecessors)
- false maps to the unit type (successor has one predecessor)

```agda

Nat-arity : Bool -> Type
Nat-arity true  = ⊥
Nat-arity false = ⊤

W-Nat : Type
W-Nat = W Bool Nat-arity

w-zero : W-Nat
w-zero = sup true absurd

w-suc : W-Nat -> W-Nat
w-suc n = sup false (λ _ -> n)

```

Recursion on W-Nat matches structural recursion on Nat.

```agda

W-Nat-rec
  : ∀ {u} {C : Type u}
  -> C
  -> (C -> C)
  -> W-Nat -> C
W-Nat-rec z s = rec step where
  step : (b : Bool) -> (Nat-arity b -> _) -> _
  step true  _ = z
  step false f = s (f tt)

```

## Lists as a W-type

Lists over A can be encoded as W (Maybe A) (maybe (const bottom) (const top)):
- nothing represents nil (no children)
- just a represents cons a (one child: the tail)

```agda

module _ {u} (A : Type u) where

  List-arity : Maybe A -> Type
  List-arity nothing  = ⊥
  List-arity (just _) = ⊤

  W-List : Type u
  W-List = W (Maybe A) List-arity

  w-nil : W-List
  w-nil = sup nothing absurd

  w-cons : A -> W-List -> W-List
  w-cons a xs = sup (just a) (λ _ -> xs)

```

Recursion on W-List matches structural recursion on List.

```agda

  W-List-rec
    : ∀ {u'} {C : Type u'}
    -> C
    -> (A -> C -> C)
    -> W-List -> C
  W-List-rec nil cons = rec step where
    step : (ma : Maybe A) -> (List-arity ma -> _) -> _
    step nothing  _ = nil
    step (just a) f = cons a (f tt)

```
