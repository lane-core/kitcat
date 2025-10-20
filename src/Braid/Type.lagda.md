```

{-# OPTIONS --safe --erased-cubical #-}

module Braid.Type where

open import Prim.Type

open import Agda.Builtin.List public
open import Prim.Data.Nat
open import Prim.Interval
open import Prim.Kan
open import Prim.Path

record Fin (n : Nat) : Type where
  constructor fin
  field
    ar : Nat
    @0 pf : suc ar ≤ℕ n

Z : Fin 1
Z = fin zero (≤s 0≤)

S : ∀ {n} → Fin n → Fin (suc n)
S {(zero)} f = Z
S {suc n} (fin ar pf) .Fin.ar = suc ar
S {suc n} (fin ar pf) .Fin.pf = ≤s pf

⊥ = Fin 0

elim : ∀ {u} {A : Type u} → ⊥ → A
elim (fin zero ())

≤suc : ∀ {m n} → m ≤ℕ n → m ≤ℕ (suc n)
≤suc 0≤ = 0≤
≤suc (≤s p) = ≤s (≤suc p)

≤inj : ∀ {m n} → suc m ≤ℕ suc n → m ≤ℕ n
≤inj (≤s p) = p

data Fin-view : ∀ {n} → Fin n → Type where
  Zero : Fin-view Z
  Suc : ∀ {n} (f : Fin (suc n)) → Fin-view f → Fin-view (S f)

initial-Z : (@0 pf : 1 ≤ℕ 1) → Z ≡ fin zero pf
initial-Z pf i = fin zero (≤-is-prop (≤s 0≤) pf i)

suc-S : ∀ {n} (f : Fin n) → S f .Fin.ar ≡ suc (f .Fin.ar)
suc-S {suc n} f = refl

unique-S : ∀ {n} (f@(fin ar pf) : Fin n) (@0 pf' : suc (suc ar) ≤ℕ suc n)
         → S f ≡ fin (suc ar) pf'
unique-S f pf i = fin (suc-S f i) {!≤-is-prop (S f .Fin.pf) pf i!} where
  test : {!!}
  test = ≤-is-prop {!!} {!pf!}

fcons : ∀ {ar n} (@0 pf : suc ar ≤ℕ n) → Fin-view (fin ar pf)
fcons {(zero)} {n = suc zero} pf = coe01 (λ i → Fin-view (initial-Z pf i)) Zero
fcons {(zero)} {n = suc (suc n)} pf = {!!}
fcons {suc ar} {n = suc n} pf = {!!}

fview : ∀ {n} (f : Fin n) → Fin-view f
fview {(zero)} f = elim f
fview {suc n} (fin ar pf) = fcons pf


length : ∀ {u} {A : Type u} → List A → Nat
length [] = 0
length (x ∷ xs) = suc (length xs)

record Vec (n : Nat) {u} (A : Type u) : Type u where
  constructor vec
  field
    encoding : List A
    @0 pf : length encoding ≡ n

nil : ∀ {u} {A : Type u} → Vec 0 A
nil .Vec.encoding = []
nil .Vec.pf = λ (@0 i : _) → 0

_:-_ : ∀ {n u} {A : Type u} → Vec n A → A → Vec (suc n) A
(xs :- x) .Vec.encoding = x ∷ Vec.encoding xs
(xs :- x) .Vec.pf = λ i → suc (Vec.pf xs i)

data Vec-view {u} {A : Type u} : {n : Nat} → Vec n A → Type u where
  Nil : Vec-view nil
  Cons : ∀ {n xs} → Vec-view {n = n} xs → ∀ x → Vec-view (xs :- x)

-- elim : ∀ {u} {A : Type u}

nat-discrete : {m n : Nat} (p q : m ≡ n) → p ≡ q
nat-discrete {(zero)} {(zero)} p q i = {!!}
nat-discrete {(zero)} {suc n} p q i = {!!}
nat-discrete {suc m} {(zero)} p q = {!!}
nat-discrete {suc m} {suc n} p q = {!!}

nil-initial : ∀ {u} {A : Type u} {n : Nat} (xs : Vec 0 A) → nil ≡ xs
nil-initial (vec [] pf) i = {!!}
nil-initial (vec (x ∷ encoding) pf) i = {!!}

cons : ∀ {u} {A : Type u} {xs : List A} {n : Nat} (pf : length xs ≡ n)
     → Vec-view (vec xs pf)
cons {xs = []} pf = {!nil!}
cons {xs = x ∷ xs} pf = {!!}

vec-view : ∀ {n u} {A : Type u} (xs : Vec n A) → Vec-view xs
vec-view {(zero)} xs = {!!}
vec-view {suc n} xs = {!!}

data Ptm : Type where
  var : Ptm
  abs : Ptm → Ptm → Ptm
  app : Ptm → Ptm → Ptm
  brd : (n : Nat) → (Vec n Ptm) → Ptm → Ptm

-- data Subst (xs ys : List Ptm) : Type where
