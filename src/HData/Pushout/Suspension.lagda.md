Suspension as a pushout.

The suspension of `A` glues two points (north and south) along paths
indexed by `A`. It is the pushout of the two constant maps from `A`
to the unit type.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Pushout.Suspension where

open import Core.Type
open import Core.Base

open import HData.Pushout.Type
import HData.Pushout.Base as Base

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

Susp : Type ℓ → Type ℓ
Susp {ℓ} A =
  Pushout {A = ⊤} {B = ⊤} {C = A} (λ _ → tt) (λ _ → tt)

north : {A : Type ℓ} → Susp A
north = inl tt

south : {A : Type ℓ} → Susp A
south = inr tt

merid : {A : Type ℓ} → A → north {A = A} ≡ south
merid a = glue a

ind
  : {A : Type ℓ} {P : Susp A → Type ℓ'}
  → (n : P north)
  → (s : P south)
  → (m : (a : A) → PathP (λ i → P (merid a i)) n s)
  → (x : Susp A) → P x
ind n s m = Base.ind _ (λ _ → n) (λ _ → s) m

rec
  : {A : Type ℓ} {X : Type ℓ'}
  → (n : X)
  → (s : X)
  → (m : A → n ≡ s)
  → Susp A → X
rec n s m = Base.rec (λ _ → n) (λ _ → s) m

map : {A : Type ℓ} {B : Type ℓ'} → (A → B) → Susp A → Susp B
map f = rec north south (λ a → merid (f a))
```
