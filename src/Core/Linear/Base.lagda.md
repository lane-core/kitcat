
```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Linear.Base where

open import Core.Type
open import Core.Data.Sigma

infix 7 _⊗_
data Res u : Type (u ₊) where
  nil : Res u
  inc : {A : Type u} → A → Res u
  _⊗_ : Res u → Res u → Res u

infix 4 _>>_
data _>>_ {u} : Res u → Res u → Type (u ₊) where
  idn : ∀ x → x >> x
  seq : ∀ {x y z} → x >> y → y >> z → x >> z
  _⊗_ : ∀ {a b x y} (f : a >> x) (g : b >> y)
      → (a ⊗ b) >> (x ⊗ y)
  assoc : ∀ {x y z} → (x ⊗ y) ⊗ z >> x ⊗ (y ⊗ z)
  swap : ∀ {x y} → x ⊗ y >> y ⊗ x
  unitr : ∀ x → x ⊗ nil >> x
  inv-unitr : ∀ x → x >> x ⊗ nil

LType : ∀ u → Type (u ₊)
LType u = Σ A ∶ Type u , (A → Res u)

infix 4 _⊩_
_⊩_ : ∀ {u} → Res u → LType u → Type (u ₊)
Δ ⊩ (A , φ) = Σ a ∶ A , Δ >> φ a

module _ {u}  where
  singleton : ∀ {A : Type u} (a : A) → inc a ⊩ (A , inc)
  singleton a = a , idn (inc a)

  idJ : {A : LType u} (x : A .fst) → inc x ⊩ A
  idJ x = x , {!idn ?!}
