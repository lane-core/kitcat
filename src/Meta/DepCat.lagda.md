```agda

{-# OPTIONS --safe --erased-cubical #-}

module Meta.DepCat where

open import Prim.Type
open import Prim.Data
open import Prim.Path
open import Trait.Graphical

open import Prop.HLevel
open import Prop.Equiv

--open imp

-- record Magmoid u v : Type₊ (u ⊔ v) where
--   field
--     Ob : Type u
--     Hom : Ob → Ob → Type v
--     seq : ∀ {x y z} → Hom x y → Hom y z → Hom x z

module Magmoid {u v}
  (Ob : Type u)
  (Hom : Ob → Ob → Type v)
  (seq : ∀ {x y z} → Hom x y → Hom y z → Hom x z)
  where
  private
    infixr 40 _∙_
    _∙_ = seq

  record is-iso {x y} (f : Hom x y) : Type (u ⊔ v) where
    field
      pre : ∀ {z} → is-equiv (λ (h : Hom y z) → f ∙ h)
      post : ∀ {w} → is-equiv (λ (h : Hom w x) → h ∙ f)

  record is-idem-equiv {x} (i : Hom x x) : Type (u ⊔ v) where
    field
      iso : is-iso i
      idem : i ∙ i ≡ i

  has-identity : Ob → Type (u ⊔ v)
  has-identity x = Σ {A = Hom x x} is-idem-equiv

record Category u v : Type₊ (u ⊔ v) where
  field
    Ob : Type u
    Hom : Ob → Ob → Type v
    seq : ∀ {x y z} → Hom x y → Hom y z → Hom x z
    identity : (x : Ob) → Magmoid.has-identity Ob Hom seq x

  idn : (x : Ob) → Hom x x
  idn x = fst (identity x)

instance
  Graphical-Category : ∀ {u v} → Graphical (Category u v)
  Graphical-Category {u} .Graphical.l₀ = u
  Graphical-Category {v} .Graphical.l₁ = v
  Graphical-Category .Graphical.∣_∣ = Category.Ob
  Graphical-Category .Graphical._[_,_] = Category.Hom

record fam-category {u v} (C : Category u v) w : Type (u ⊔ v ⊔ w ₊) where
  private module C = Category C
  field
    fHom : ∣ C ∣ → Type w
    fseq : {x y : ∣ C ∣} → C [ x , y ] → fHom y → fHom x
    fseq-idn : {x : ∣ C ∣} (ι : fHom x) → fseq (C.idn x) ι ≡ ι
    fseq-comp : {x y z : ∣ C ∣} (f : C [ x , y ]) (g : C [ y , z ]) (ι : fHom z)
              → fseq (C.seq f g) ι ≡ fseq f (fseq g ι)

Σ A (λ c → (∀ x → c = x))
≃

syntactically the derivation would work like this:

we have this in the context (besides Nat and Bin):
```
half2 :: Nat -> Nat
mul2 :: Nat -> Nat
half-dbl :: ∀x.(half2(mul2(x)) == x)
eqv :: Nat ≃ Bin (contains f :: Nat -> Bin)
ua :: ∀A.∀B.(A ≃ B -> A = B)
tr :: ∀A.∀(P : A -> Type).∀x.∀y.(x == y -> P x -> P y)
```

We can quickly derive the following

```

def exp_eq() : Type{(Nat -> Nat) == (Bin -> Bin)}:
  tr Type (\x -> Type{(x -> x) == (Bin -> Bin)}) Nat Bin (ua Nat Bin eqv)


```

and if we

∀x.half2(mul2(x))==x from x:Nat to x:Bin
```


record cofam-category {u v} (C : Category u v) w : Type (u ⊔ v ⊔ w ₊) where
  private module C = Category C
  field
    cfHom : ∣ C ∣ → Type w
    cfseq : {x y : ∣ C ∣} → cfHom x → C [ x , y ] → cfHom y
    cfseq-idn : {x : ∣ C ∣} (ι : cfHom x) → cfseq ι (C.idn x) ≡ ι
    cfseq-comp : {x y z : ∣ C ∣} (f : C [ x , y ]) (g : C [ y , z ]) (ι : cfHom x)
               → cfseq ι (C.seq f g) ≡ cfseq (cfseq ι f) g
