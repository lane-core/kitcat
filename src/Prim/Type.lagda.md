```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Type where

open import Agda.Primitive public
  using ( SSet
        ; SSetω
        ; LevelUniv
        ; Level )
  renaming ( Set   to Type
           ; Setω  to Typeω
           ; _⊔_ to infixl 6 _⊔_
           ; lsuc to infixr 7 _₊
           ; lzero to 0ℓ )

record Lift {u} ℓ (A : Type u) : Type (u ⊔ ℓ) where
  constructor lift
  field
    lower : A

open Lift public

1ℓ : Level
1ℓ = 0ℓ ₊

level-of : ∀ {ℓ} {A : Type ℓ} → A → Level
level-of {ℓ} _ = ℓ

Type₊ : ∀ ℓ → Type (ℓ ₊ ₊)
Type₊ ℓ = Type (ℓ ₊)

𝓤 : Typeω
𝓤 = (u : Level) → Type u

record Erased {u} (@0 A : Type u) : Type u where
  constructor erase
  field
    @0 erased : A

open Erased public

record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀ : ∀ {ℓ} → Type ℓ → Type (adj ℓ)

infixr 8 Λ-syntax

Λ-syntax : {M : Effect} (let module M = Effect M)
         → (∀ {u} (A : Type u) → A → M.₀ A)
         → ∀ {u} {A : Type u} → A → M.₀ A
Λ-syntax f {A} = f A
{-# INLINE Λ-syntax #-}

syntax Λ-syntax (λ A → B) = Λ A ∎ B

```

Empty type and Negation

```

module ⊥ where
  data ⊥ : Type where
  open ⊥ public

  ind : ∀ {u} (@0 P : ⊥ → Type u) → (@0 e : ⊥) → P e
  ind P ()

open ⊥ using (⊥) hiding (module ⊥) public

infixl 5 ¬_

ex-falso : ∀ {u} {@0 A : Type u} → (@0 e : ⊥) → A
ex-falso {A = A} = ⊥.ind (λ _ → A)

¬_ : ∀ {u} → Type u → Type u
¬ A = A → ⊥

¬¬_ : ∀ {u} → Type u → Type u
¬¬_ A = ¬ (¬ A)

--¬¬intro :

module ⊤ where
  open import Agda.Builtin.Unit hiding (module ⊤) public
  open Agda.Builtin.Unit.⊤ public

  ind : ∀ {u} (P : @0 ⊤ → Type u) (p : P tt) → (@0 x : ⊤) → P x
  ind P p ._ = p

open ⊤ using (⊤; tt) public

Π : ∀ {u v} {A : Type u} → (A → Type v) → Type (u ⊔ v)
Π B = ∀ x → B x

id : ∀ {u} {@0 A : Type u} → A → A
id = λ x → x
{-# INLINE id #-}

idf : ∀ {u} (@0 A : Type u) → A → A
idf A = λ x → x
{-# INLINE idf #-}

const : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A → B → A
const a ._ = a
{-# INLINE const #-}

rconst : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A → B → B
rconst ._ b = b
{-# INLINE rconst #-}

funcomp : ∀ {u v w} {@0 A : Type u} {@0 B : Type v} {@0 C : B → Type w}
     → ((y : B) → C y) → (f : A → B) (x : A) → C (f x)
funcomp g f = λ x → g (f x)
{-# INLINE funcomp #-}

infixr -1 _$_ _$ₑ_ _$ᵢ_ -- _$ₛ_

_$_ : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v} → ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}

@0 _$ₑ_ : ∀ {u v} {@0 A : Type u} {@0 B : @0 A → Type v} → @0 ((x : A) → B x) → ((x : A) → B x)
@0 f $ₑ x = f x
{-# INLINE _$ₑ_ #-}

_$ᵢ_ : ∀ {u v} {@0 A : Type u} {@0 B : .A → Type v} → (.(x : A) → B x) → (.(x : A) → B x)
f $ᵢ x = f x
{-# INLINE _$ᵢ_ #-}

-- _$ₛ_ : ∀ {u v} {A : Type u} {B : A → SSet v} → ((x : A) → B x) → ((x : A) → B x)
-- f $ₛ x = f x
-- {-# INLINE _$ₛ_ #-}

all-syntax : {adj : Level → Level} {F : ∀ {u} → Type u → Type (adj u)}
         → (∀ {u} (A : Type u) → A → F A)
         → ∀ {u} {A : Type u} → A → F A
all-syntax f {A} = f A

syntax all-syntax (λ A → B) = Λ A => B
infixr 8 all-syntax
