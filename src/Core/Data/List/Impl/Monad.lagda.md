Monad instance for List.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Impl.Monad where

open import Core.Type
open import Core.Data.List.Type
open import Core.Data.List.Base
open import Core.Data.List.Properties
open import Core.Data.List.Impl.Applicative
open import Core.Trait.Effect
open import Core.Trait.Monad using (Monad)

instance
  Monad-List : Monad (impl List)
  Monad-List .Monad.Applicative-Monad = Applicative-List
  Monad-List .Monad._>>=_ xs f = concatMap f xs
  Monad-List .Monad.>>=-left-id {f = f} =
    concatMap.singleton f _
  Monad-List .Monad.>>=-right-id {m = m} = concatMap.unitr m
  Monad-List .Monad.>>=-assoc {m = m} {f} {g} =
    concatMap.assoc f g m

```
