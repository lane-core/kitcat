```agda

{-# OPTIONS --safe --erased-cubical #-}

module Lib.Core.Type where

open import Lib.Core.Prim
open import Lib.Core.Num public

data _⊎_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr -1 _⊎_

```
Empty type and Negation
```

module Void where
  data ⊥ : Type where

  ind : ∀ {u} (@0 P : ⊥ → Type u) (@0 e : ⊥) → P e
  ind P ()

  Void : ∀ {u} → Type u
  Void {u} = Lift u ⊥

open Void using (⊥) public

infixl 5 ¬_

ex-falso : ∀ {u} {@0 A : Type u} → (@0 e : ⊥) → A
ex-falso {A = A} = Void.ind (λ _ → A)

¬_ : ∀ {u} → Type u → Type u
¬ A = A → ⊥

Not = ¬_
{-# DISPLAY Not A = ¬ A #-}

¬¬_ : ∀ {u} → Type u → Type u
¬¬_ A = ¬ (¬ A)

```
For the Sigma type from Agda.Builtin we'll use TypeTopology's shortened
notation because its far more convenient. We can use textbook style Sigma
notation if we want to annotate the type of `fst` using the Σ-syntax
definition.
```

open import Agda.Builtin.Sigma public
  renaming ( Σ to Sigma
           ; _,_ to infixr 4 _,_ )
  using (fst; snd; module Σ) -- keep the module the same name, it works

Σ : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ {A = A} B = Sigma A B
{-# INLINE Σ #-}
{-# INLINE _,_ #-}
{-# DISPLAY Sigma _ B = Σ B #-}

infixr 4 _×_
_×_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
_×_ A B = Sigma A (λ _ → B)

dup : ∀ {u} {@0 A : Type u} → A → A × A
dup a = a , a
{-# INLINE dup #-}

swap : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A × B → B × A
swap (a , b) = b , a
{-# INLINE swap #-}

Σ-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄
         → (X : A) (F : ⌞ X ⌟ → Type ℓ') → Type _
Σ-syntax X F = Sigma ⌞ X ⌟ F
infixr -1 Σ-syntax
syntax Σ-syntax A (λ x → M) = Σ x ∶ A , M
{-# DISPLAY Σ-syntax _ B = Σ B #-}

instance
  Underlying-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
               → ⦃ ua : Underlying A ⦄
               → Underlying (Σ B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟ x = ⌞ x .fst ⌟

```
Booleans
```
module Bool where
  open import Agda.Builtin.Bool public
    renaming (true to tt; false to ff)
    hiding (module Bool)

  open Agda.Builtin.Bool.Bool public

  not : Bool → Bool
  not ff = tt
  not tt = ff
  {-# INLINE not #-}

  and : Bool → Bool → Bool
  and ff b = ff
  and tt b = b
  {-# INLINE and #-}

  or : Bool → Bool → Bool
  or ff b = b
  or tt b = tt
  {-# INLINE or #-}

  if-then-else : ∀ {u} {@0 P : Bool → Type u} (b : Bool) → P tt → P ff → P b
  if-then-else ff x y = y
  if-then-else tt x y = x
  {-# INLINE if-then-else #-}

open Bool public
  using (Bool; tt; ff)
  renaming (and to _&&_)

data Res {u v} (A : Type u) (B : A → Type v) : Type (u ⊔ v) where
  _#_ : (val : A) → B val → Res A B

Type* : ∀ u → Type (u ₊)
Type* u = Σ A ∶ Type u , A

instance
  Underlying-Pointed : ∀ {u} → Underlying (Type* u)
  Underlying-Pointed {u} .Underlying.ℓ-underlying = u
  Underlying-Pointed .Underlying.⌞_⌟ A = A .fst

open import Agda.Builtin.Strict public
  renaming (primForce to force; primForceLemma to force-lemma)

import Agda.Builtin.Equality; module Id = Agda.Builtin.Equality

import Agda.Builtin.String; module String = Agda.Builtin.String
  renaming ( primStringUncons to uncons
           ; primStringToList to to-list
           ; primStringFromList to from-list
           ; primStringAppend to append
           ; primStringEquality to Eq
           ; primShowChar to show-char
           ; primShowString to show-string
           ; primShowNat to show-nat
           )
open String using (String)

open import Agda.Builtin.FromString public
  renaming (IsString to FromString)

import Agda.Builtin.Char; module Char = Agda.Builtin.Char
open Char using (Char) public

import Agda.Builtin.Float; module Float = Agda.Builtin.Float
open Float using (Float) public

open import Agda.Builtin.Maybe public

import Agda.Builtin.Word ; module Word64 = Agda.Builtin.Word
  renaming (primWord64ToNat to to-nat; primWord64FromNat to from-nat)
open Word64 using (Word64) public

open import Agda.Builtin.List public

data SnocList {u} (A : Type u) : Type u where
  [] : SnocList A
  _∶<_ : SnocList A → A → SnocList A

