Alternative instance for List.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Impl.Alternative where

open import Core.Type
open import Core.Base using (_≡_; refl)
open import Core.Data.List.Type
open import Core.Data.List.Base
open import Core.Data.List.Properties
open import Core.Data.List.Impl.Applicative
open import Core.Trait.Effect
open import Core.Trait.Alternative using (Alternative)

instance
  Alternative-List : Alternative (impl List)
  Alternative-List .Alternative.Applicative-Alternative =
    Applicative-List
  Alternative-List .Alternative.empty = []
  Alternative-List .Alternative._<|>_ = _++_
  Alternative-List .Alternative.<|>-left-id = refl
  Alternative-List .Alternative.<|>-right-id {x = x} =
    cat.unitr x
  Alternative-List .Alternative.<|>-assoc {x = x} {y} {z} =
    cat.assoc x y z

```
