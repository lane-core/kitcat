Map instance for List.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Impl.Map where

open import Core.Type
open import Core.Base using (funext)
open import Core.Data.List.Type
open import Core.Data.List.Base
open import Core.Data.List.Properties
open import Core.Trait.Effect
open import Core.Trait.Map using (Map)

instance
  Map-List : Map (impl List)
  Map-List .Map.map = map
  Map-List .Map.map-id = funext map.id
  Map-List .Map.map-comp {f = f} {g} = funext (map.comp f g)

```
