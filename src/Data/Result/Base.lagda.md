Operations on dependent tagged pairs.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Result.Base where

open import Core.Type
open import Core.Data.Sigma

open import Data.Result.Type

val : ∀ {u v} {A : Type u} {B : A -> Type v} -> Res A B -> A
val (a # _) = a
{-# INLINE val #-}

payload : ∀ {u v} {A : Type u} {B : A -> Type v}
        -> (r : Res A B) -> B (val r)
payload (_ # b) = b
{-# INLINE payload #-}

ind : ∀ {u v w} {A : Type u} {B : A -> Type v}
    -> (P : Res A B -> Type w)
    -> ((a : A) (b : B a) -> P (a # b))
    -> (r : Res A B) -> P r
ind P f (a # b) = f a b
{-# INLINE ind #-}

map : ∀ {u v w} {A : Type u} {B : A -> Type v} {C : A -> Type w}
    -> (∀ {a} -> B a -> C a) -> Res A B -> Res A C
map f (a # b) = a # f b

bimap : ∀ {u u' v w} {A : Type u} {A' : Type u'}
          {B : A -> Type v} {C : A' -> Type w}
      -> (f : A -> A') -> (∀ {a} -> B a -> C (f a))
      -> Res A B -> Res A' C
bimap f g (a # b) = f a # g b

to-sigma : ∀ {u v} {A : Type u} {B : A -> Type v}
          -> Res A B -> Σ B
to-sigma (a # b) = a , b

from-sigma : ∀ {u v} {A : Type u} {B : A -> Type v}
            -> Σ B -> Res A B
from-sigma (a , b) = a # b

```
