Homotopy levels: contractibility, propositions, sets, and truncation.

This module re-exports Core.Trait.Trunc (which provides is-hlevel and the Trunc
automation) and adds additional proofs and utilities.

The H-Level automation machinery is largely derived from 1Lab (Amélia Liao et al.),
with additional influence from Chen's semicategories-with-identities formalization.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.HLevel where

open import Core.Data.Nat 
open import Core.Data.Fin using (Fin)
open import Core.Data.Maybe using (Maybe; nothing; just)
open import Core.Transport
open import Core.Equiv
open import Core.Base
open import Core.Path
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Sum
open import Core.Data.Bool
open import Core.Type
open import Core.Kan
open import Core.Sub


-- Re-export the Trunc trait and is-hlevel definitions
open import Core.Trait.Trunc public

private variable
  u v : Level
  A B : Type u

is-groupoid : ∀ {u} → Type u → Type u
is-groupoid = is-hlevel 3


-- N-type: bundled truncated types

record N-type u n : Type₊ u where
  no-eta-equality
  field
    ∣_∣ : Type u
    trunc-ntype : is-hlevel n ∣_∣

{-# INLINE N-type.constructor #-}

-- Additional proofs

PathP-is-hlevel'
  : ∀ {u} {A : I → Type u} {n} {x : A i0} {y : A i1}
  → ((i : I) → is-hlevel (S n) (A i)) → is-hlevel n (PathP A x y)
PathP-is-hlevel' hl = PathP-is-hlevel (hl i1)

equiv→is-hlevel
  : ∀ {u v} {A : Type u} {B : Type v} (n : Nat)
  → A ≃ B → is-hlevel n A → is-hlevel n B
equiv→is-hlevel n e =
  retract→is-hlevel n (Equiv.fwd e) (Equiv.inv e) (Equiv.counit e)

is-prop-×
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-prop A → is-prop B → is-prop (A × B)
is-prop-× aprop bprop (a , b) (a' , b') i = aprop a a' i , bprop b b' i

is-prop-equiv
  : ∀ {u v} {A : Type u} {B : Type v}
  → A ≃ B → is-prop B → is-prop A
is-prop-equiv e bprop x y = equiv-path
  where
    module E = Equiv e
    equiv-path : x ≡ y
    equiv-path = sym (E.unit x) ∙ ap E.inv (bprop (E.fwd x) (E.fwd y)) ∙ E.unit y

singl-contr-in-contr
  : ∀ {u} {A : Type u}
  → is-contr A → (x : A) → is-contr (Σ y ∶ A , x ≡ y)
singl-contr-in-contr c x .center = x , refl
singl-contr-in-contr c x .paths (y , p) = Σ-prop-path (is-contr→is-set c x) p

subst-prop
  : ∀ {u u'} {A : Type u} {P : A → Type u'}
  → is-prop A → ∀ a → P a → ∀ b → P b
subst-prop {P = P} prop a pa b = subst P (prop a b) pa

contr→contr-fiber
  : ∀ {u u'} {A : Type u} {B : Type u'}
  → (f : A → B) → is-contr A → is-contr B
  → ∀ b → is-contr (Σ a ∶ A , f a ≡ b)
contr→contr-fiber {A = A} f acontr bcontr b =
  prop-inhabited→is-contr fiber-is-prop fiber-inhabited
  where
    β : (x : A) → is-prop (f x ≡ b)
    β x f g = is-contr→is-set bcontr _ _ f g

    fiber-is-prop : is-prop (Σ a ∶ A , f a ≡ b)
    fiber-is-prop (a₁ , p₁) (a₂ , p₂) =
      Σ-prop-path β (is-contr→is-prop acontr a₁ a₂)

    fiber-inhabited : Σ a ∶ A , f a ≡ b
    fiber-inhabited = acontr .center , is-contr→is-prop bcontr _ _


-- H-level closure lemmas from Rijke (Sections 12-13)

-- Propositions are closed under implication
-- (Π-is-prop is in Core.Trait.Trunc)
→-is-prop
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-prop B → is-prop (A → B)
→-is-prop bprop = Π-is-prop (λ _ → bprop)

-- Sets are closed under Π
-- This is a special case of Π-is-hlevel at level 2
Π-is-set
  : ∀ {u v} {A : Type u} {B : A → Type v}
  → ((x : A) → is-set (B x))
  → is-set ((x : A) → B x)
Π-is-set bset f g =
  retract→is-hlevel 1 funext happly (λ _ → refl)
    (Π-is-prop (λ x → bset x (f x) (g x)))

-- Sets are closed under →
→-is-set
  : ∀ {u v} {A : Type u} {B : Type v}
  → is-set B → is-set (A → B)
→-is-set bset = Π-is-set (λ _ → bset)

-- Σ over a set with set fibers is a set
-- (This is a special case of Σ-is-hlevel from Core.Trait.Trunc)
Σ-is-set
  : ∀ {u v} {A : Type u} {B : A → Type v}
  → is-set A → ((x : A) → is-set (B x))
  → is-set (Σ B)
Σ-is-set aset bset = Σ-is-hlevel 2 aset bset
```


## Proposition Utilities

```agda

-- Paths in propositions are contractible
is-prop→Path-is-contr
  : ∀ {u} {A : Type u}
  → is-prop A → (x y : A) → is-contr (x ≡ y)
is-prop→Path-is-contr aprop x y =
  prop-inhabited→is-contr (is-prop→is-set aprop x y) (aprop x y)

-- Propositions are closed under retraction
-- If B is a retract of A (via section f : A → B) and A is a prop, then B is a prop.
-- The condition is: f (g b) ≡ b for all b : B (g is a section of f).
retract→is-prop
  : ∀ {u' v'} {A' : Type u'} {B' : Type v'}
  → (f : A' → B') (g : B' → A')
  → is-left-inverse f g
  → is-prop A' → is-prop B'
retract→is-prop f g r aprop = retract→is-hlevel 1 f g r aprop
```


## Type-Specific H-Level Proofs

### Bool

```agda

open import Core.Data.Dec
```

### Sum Types

Sum types preserve h-levels. The key insight is that paths in sum types
decompose: paths between inl's come from paths in A, paths between inr's
from paths in B, and paths between inl and inr are impossible.

```agda

module _ {u' v'} {A' : Type u'} {B' : Type v'} where
  private
    module inl-path {a a' : A'} = Equiv (⊎-path-inl {B = B'} {a = a} {a' = a'})
    module inr-path {b b' : B'} = Equiv (⊎-path-inr {A = A'} {b = b} {b' = b'})

    -- Helper for inl-inl paths
    inl-inl-hlevel
      : (n : Nat) → is-hlevel (S (S n)) A'
      → (a a' : A') → is-hlevel (S n) (inl {B = B'} a ≡ inl a')
    inl-inl-hlevel n ahl a a' =
      retract→is-hlevel (S n) encode decode linv (Path-is-hlevel {x = a} {y = a'} ahl)
      where
        encode : a ≡ a' → inl {B = B'} a ≡ inl a'
        encode = inl-path.inv

        decode : inl {B = B'} a ≡ inl a' → a ≡ a'
        decode = inl-path.fwd

        linv : (p : inl {B = B'} a ≡ inl a') → encode (decode p) ≡ p
        linv = inl-path.unit

    -- Helper for inr-inr paths
    inr-inr-hlevel
      : (n : Nat) → is-hlevel (S (S n)) B'
      → (b b' : B') → is-hlevel (S n) (inr {A = A'} b ≡ inr b')
    inr-inr-hlevel n bhl b b' =
      retract→is-hlevel (S n) encode decode linv (Path-is-hlevel {x = b} {y = b'} bhl)
      where
        encode : b ≡ b' → inr {A = A'} b ≡ inr b'
        encode = inr-path.inv

        decode : inr {A = A'} b ≡ inr b' → b ≡ b'
        decode = inr-path.fwd

        linv : (p : inr {A = A'} b ≡ inr b') → encode (decode p) ≡ p
        linv = inr-path.unit

    inl-inr-hlevel
      : (n : Nat) → (a : A') (b : B')
      → is-hlevel (S n) (inl a ≡ inr b)
    inl-inr-hlevel n a b = is-prop→is-hlevel-suc {n = n}
      (λ p _ → ex-falso (⊎-disjoint p))

    inr-inl-hlevel
      : (n : Nat) → (b : B') (a : A')
      → is-hlevel (S n) (inr b ≡ inl a)
    inr-inl-hlevel n b a = is-prop→is-hlevel-suc {n = n}
      (λ p _ → ex-falso (⊎-disjoint (sym p)))

  ⊎-is-hlevel
    : (n : Nat)
    → is-hlevel (S (S n)) A' → is-hlevel (S (S n)) B'
    → is-hlevel (S (S n)) (A' ⊎ B')
  ⊎-is-hlevel n ahl bhl (inl a) (inl a') = inl-inl-hlevel n ahl a a'
  ⊎-is-hlevel n ahl bhl (inl a) (inr b) = inl-inr-hlevel n a b
  ⊎-is-hlevel n ahl bhl (inr b) (inl a) = inr-inl-hlevel n b a
  ⊎-is-hlevel n ahl bhl (inr b) (inr b') = inr-inr-hlevel n bhl b b'
```

### Maybe

Maybe is defined as `Maybe A ≃ ⊤ ⊎ A`, so it inherits h-levels from sums.
Like sums, Maybe preserves h-levels at the set level and above.

```agda

-- Maybe A is equivalent to ⊤ ⊎ A
Maybe-equiv-⊎ : ∀ {u''} {A'' : Type u''} → Maybe A'' ≃ (⊤ ⊎ A'')
Maybe-equiv-⊎ {A'' = A''} = iso→equiv to from linv rinv
  where
    to : Maybe A'' → ⊤ ⊎ A''
    to nothing = inl tt
    to (just a) = inr a

    from : ⊤ ⊎ A'' → Maybe A''
    from (inl _) = nothing
    from (inr a) = just a

    linv : (x : Maybe A'') → from (to x) ≡ x
    linv nothing = refl
    linv (just a) = refl

    rinv : (y : ⊤ ⊎ A'') → to (from y) ≡ y
    rinv (inl tt) = refl
    rinv (inr a) = refl

Maybe-is-hlevel
  : ∀ {u''} {A'' : Type u''} (n : Nat)
  → is-hlevel (S (S n)) A'' → is-hlevel (S (S n)) (Maybe A'')
Maybe-is-hlevel {A'' = A''} n ahl =
  equiv→is-hlevel (S (S n)) (esym Maybe-equiv-⊎) sum-hlevel
  where
    ⊤-hlevel : is-hlevel (S (S n)) ⊤
    ⊤-hlevel = is-contr→is-hlevel (S (S n)) (Contr tt (λ _ → refl))

    sum-hlevel : is-hlevel (S (S n)) (⊤ ⊎ A'')
    sum-hlevel = ⊎-is-hlevel n ⊤-hlevel ahl
```

### List

Lists are sets when their element type is a set. More generally,
`List A` is (S (S n))-truncated when A is (S (S n))-truncated.

```agda

open import Core.Data.List

-- Helper: cons is injective
cons-injective
  : ∀ {u} {A : Type u} {x y : A} {xs ys : List A}
  → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
cons-injective {x = x} {xs = xs} p = ap head' p , ap tail' p
  where
    head' : List _ → _
    head' [] = x  -- default, unreachable in our use case
    head' (z ∷ _) = z

    tail' : List _ → List _
    tail' [] = xs  -- default, unreachable in our use case
    tail' (_ ∷ zs) = zs

List-is-hlevel
  : ∀ {u} {A : Type u} (n : Nat)
  → is-hlevel (S (S n)) A → is-hlevel (S (S n)) (List A)
List-is-hlevel {A = A} n ahl [] [] =
  is-contr→is-hlevel (S n) nil-path-contr
  where
    -- Code for paths starting from []
    Code : List A → Type
    Code [] = ⊤
    Code (_ ∷ _) = ⊥

    encode : (xs : List A) → [] ≡ xs → Code xs
    encode _ p = subst Code p tt

    decode : (xs : List A) → Code xs → [] ≡ xs
    decode [] _ = refl
    decode (_ ∷ _) ()

    decode-encode : (xs : List A) (p : [] ≡ xs) → decode xs (encode xs p) ≡ p
    decode-encode _ p = J (λ y q → decode y (encode y q) ≡ q)
                          (ap (decode []) (transport-refl tt)) p

    nil-path-contr : is-contr ([] ≡ [])
    nil-path-contr .center = refl
    nil-path-contr .paths p = decode-encode [] p

List-is-hlevel n ahl [] (y ∷ ys) =
  is-prop→is-hlevel-suc {n = n} (λ p _ → ex-falso (subst discrim p tt))
  where discrim : List _ → Type; discrim [] = ⊤; discrim (_ ∷ _) = ⊥
List-is-hlevel n ahl (x ∷ xs) [] =
  is-prop→is-hlevel-suc {n = n} (λ p _ → ex-falso (subst discrim p tt))
  where discrim : List _ → Type; discrim [] = ⊥; discrim (_ ∷ _) = ⊤
List-is-hlevel n ahl (x ∷ xs) (y ∷ ys) =
  equiv→is-hlevel (S n) (esym List-cons-path-equiv) inner
  module ListCons where
    -- Code family for paths from x ∷ xs
    Code : List _ → Type _
    Code [] = Lift _ ⊥
    Code (z ∷ zs) = (x ≡ z) × (xs ≡ zs)

    encode : (zs : List _) → (x ∷ xs) ≡ zs → Code zs
    encode _ p = subst Code p (refl , refl)

    decode : (zs : List _) → Code zs → (x ∷ xs) ≡ zs
    decode [] (liftℓ ())
    decode (z ∷ zs) (p , q) i = p i ∷ q i

    decode-encode : (zs : List _) (p : (x ∷ xs) ≡ zs) → decode zs (encode zs p) ≡ p
    decode-encode _ p = J (λ zs' q → decode zs' (encode zs' q) ≡ q)
                          (ap (decode _) (transport-refl _)) p

    encode-decode : (zs : List _) (c : Code zs) → encode zs (decode zs c) ≡ c
    encode-decode [] (liftℓ ())
    encode-decode (z ∷ zs) c =
      J2 (λ z' zs' q r →
          encode (z' ∷ zs') (decode (z' ∷ zs') (q , r)) ≡ (q , r))
        (transport-refl _) (c .fst) (c .snd)
      where
        J2
          : {a : _} {as : List _}
          → (P : (b : _) (bs : List _) → a ≡ b → as ≡ bs → Type _)
          → P a as refl refl
          → (p : a ≡ z) (q : as ≡ zs) → P z zs p q
        J2 {a} {as} P pr p q =
          J (λ b p' → P b zs p' q) (J (λ bs q' → P a bs refl q') pr q) p

    -- Paths in x ∷ xs ≡ y ∷ ys are equivalent to pairs of component paths
    List-cons-path-equiv : ((x ∷ xs) ≡ (y ∷ ys)) ≃ ((x ≡ y) × (xs ≡ ys))
    List-cons-path-equiv = iso→equiv (encode (y ∷ ys)) (decode (y ∷ ys))
      (decode-encode (y ∷ ys)) (encode-decode (y ∷ ys))

    inner : is-hlevel (S n) ((x ≡ y) × (xs ≡ ys))
    inner = ×-is-hlevel (S n) (ahl x y) (List-is-hlevel n ahl xs ys)
```


## Trunc Instances for Data Types

```agda

instance
  Trunc-Bool : ∀ {k} → Trunc Bool (S (S k))
  Trunc-Bool = set-trunc Bool.set

  Trunc-⊎
    : ∀ {u' v'} {A' : Type u'} {B' : Type v'} {n}
    → ⦃ Trunc A' (S (S n)) ⦄ → ⦃ Trunc B' (S (S n)) ⦄
    → Trunc (A' ⊎ B') (S (S n))
  Trunc-⊎ {n = n} .has-trunc = ⊎-is-hlevel n (trunc (S (S n))) (trunc (S (S n)))

  Trunc-Maybe
    : ∀ {u''} {A'' : Type u''} {n}
    → ⦃ Trunc A'' (S (S n)) ⦄
    → Trunc (Maybe A'') (S (S n))
  Trunc-Maybe {n = n} .has-trunc = Maybe-is-hlevel n (trunc (S (S n)))

  Trunc-List
    : ∀ {u} {A : Type u} {n}
    → ⦃ Trunc A (S (S n)) ⦄
    → Trunc (List A) (S (S n))
  Trunc-List {n = n} .has-trunc = List-is-hlevel n (trunc (S (S n)))

  Trunc-Fin : ∀ {m k} → Trunc (Fin m) (S (S k))
  Trunc-Fin = set-trunc Fin.set

{-# OVERLAPS Trunc-Bool Trunc-Fin #-}
```
