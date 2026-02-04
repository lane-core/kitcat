Lane Biocini
October 2025

Path algebra: symmetry, concatenation, squares, and coherences.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Path where

open import Core.Transport
open import Core.Base
open import Core.Type
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Sum
open import Core.Data.Pointed
open import Core.Kan
open import Core.Sub

private
  variable
    u v : Level
    A : I → Type u

idp : {A : Type u} {x : A} → x ≡ x
idp {x = x} = λ _ → x

dsym : {x : A i0} {y : A i1} → x ≡ y ∶ A → y ≡ x ∶ (λ i → A (~ i))
dsym q i = q (~ i)

hpcom : {A : Type u} {x y z : A} {p q : x ≡ y} {r s : y ≡ z}
      → p ≡ q → r ≡ s → _∙_ p r ≡ _∙_ q s
hpcom α β i = _∙_ (α i) (β i)

cong2 : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
    → (f : A → B → C)
    → {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ≡ a₂
    → b₁ ≡ b₂
    → f a₁ b₁ ≡ f a₂ b₂
cong2 f {a₁} {a₂} {b₁} {b₂} p q = (ap (λ a → f a b₁) p) ∙ (ap (λ b → f a₂ b) q)

erefl : ∀ {u} {A : Type u} (x : A) → x ≡ x
erefl x = refl {x = x}

Singl : ∀ {u} {A : Type u} → A → Type u
Singl {A = A} x = Σ (λ a → (x ≡ a))
{-# INLINE Singl #-}

×-to-path : ∀ {u} {A : Type u} → {w x y z : A} → w ≡ y → x ≡ z → (w , x) ≡ (y , z)
×-to-path = cong2 _,_

Ω : ∀ {u} → Type* u → Type u
Ω (_ , a) = a ≡ a
{-# INLINE Ω #-}

Loop : ∀ {u} → Type* u → Type* u
Loop A .fst = Ω A
Loop A .snd = refl

record is-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B → A
    unit : (x : A) → inv (f x) ≡ x
    counit : (y : B) → f (inv y) ≡ y

{-# INLINE is-qinv.constructor #-}

Qinv : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Qinv A B = Σ (λ (f : A → B) → is-qinv f)
infix 6 Qinv

infix 4 _≢_
_≢_ : {A : Type u} → A → A → Type u
x ≢ y = ¬ (x ≡ y)

idtofun : ∀ {u} {A B : Type u} → A ≡ B → A → B
idtofun = subst (λ x → x)

ap0 : {@0 A : Type u} {@0 B : A → Type v} (f : ∀ (@0 x) → B x)
    → {@0 x y : A} (@0 p : x ≡ y)
    → PathP (λ i → B (p i)) (f x) (f y)
ap0 f p i = f (p i)

apd : {A : I → Type u} {B : ∀ i → A i → Type v}
    → (f : ∀ i (a : A i) → B i a)
    → {x : A i0} {y : A i1} (p : PathP A x y)
    → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
apd f p i = f i (p i)


lhs : {A : Type u} {x y : A} (p : x ≡ y) → p ≡ refl ∶ ∂.square _≡_ p refl
lhs p i j = p (i ∨ j)
{-# INLINE lhs #-}

rhs : {A : Type u} {x y : A} (p : x ≡ y) → refl ≡ p ∶ ∂.square _≡_ refl p
rhs p i j = p (i ∧ j)
{-# INLINE rhs #-}

module Path {A : Type u} where
  open cat
  hsqueeze : {x y : A} {p q : x ≡ y} → p ∙ refl ≡ refl ∙ q → p ≡ q
  hsqueeze {p} {q} h = pcom (eqvr p) h (eqvl q)

  vsqueeze : {x y : A} {p q : x ≡ y} → refl ∙ p ≡ q ∙ refl → p ≡ q
  vsqueeze {p} {q} h = pcom (eqvl p) h (eqvr q)

  paste-refl : {w x y z : A}
         → (p : w ≡ x) (q : w ≡ y) (r : y ≡ z) (s : x ≡ z) (c : x ≡ y)
         → (H : Square p refl q c)
         → (K : Square s c r refl)
         → p ∙ s ≡ q ∙ r
  paste-refl {w} {x} {y} {z} p q r s c H K i j = hcom (∂ j ∨ ~ i) λ where
    k (j = i0) → w
    k (i = i0) → cat.fill p s j k
    k (j = i1) → K i k
    k (k = i0) → H i j

  lwhisker : {x y z : A} (p : x ≡ y) {q r : y ≡ z} → q ≡ r → p ∙ q ≡ p ∙ r
  lwhisker p = ap (p ∙_)

  rwhisker : {x y z : A} {p q : x ≡ y} (r : y ≡ z) → p ≡ q → p ∙ r ≡ q ∙ r
  rwhisker r = ap (_∙ r)

  loop-refl : {x y : A} (p : x ≡ y) (q : y ≡ y)
            → Square p refl p q → q ≡ refl
  loop-refl p q sq i j = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → conn p q j k
    k (i = i1) → p (j ∨ k)
    k (j = i0) → p k
    k (j = i1) → q (i ∨ k)
    k (k = i0) → sq i j

  commutes : {w x y z : A}
           → (p : w ≡ x) (q : x ≡ z) (r : w ≡ y) (s : y ≡ z)
           → Square p r s q → p ∙ q ≡ r ∙ s
  commutes {w} p q r s sq i j = hcom (∂ j ∨ ~ i) λ where
    k (j = i0) → p (~ i ∧ ~ k)
    k (j = i1) → s (~ i ∨ k)
    k (i = i0) → rfill p q j k
    k (k = i0) → sq j (~ i)

path-idem : ∀ {u} {A : Type u} (x : A) → refl ∙ refl ≡ refl {x = x}
path-idem x i = HComposite.unique (refl {x = x}) refl refl
  (refl ∙ refl , λ j k → cat.fill (refl {x = x}) refl j k) (refl , refl) i .fst

Ext : ∀ {u} (A : I → Type u) (x : A i0) → Type u
Ext A x = Σ y ∶ A i1 , PathP A x y

module HComposite₄ {u} {A : Type u} {v w x y z : A} (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z) where
  final : v ≡ z
  final = p ∙ (q ∙ (r ∙ s))

  alt₁ : v ≡ z
  alt₁ = (p ∙ q) ∙ (r ∙ s)

  alt₂ : v ≡ z
  alt₂ = ((p ∙ q) ∙ r) ∙ s

  alt₃ : v ≡ z
  alt₃ = (p ∙ (q ∙ r)) ∙ s

  alt₄ : v ≡ z
  alt₄ = p ∙ ((q ∙ r) ∙ s)

  a→1 : final ≡ alt₁
  a→1 = assoc p q (r ∙ s)

  a1→2 : alt₁ ≡ alt₂
  a1→2 = assoc (p ∙ q) r s

  a→4 : final ≡ alt₄
  a→4 = ap (p ∙_) (assoc q r s)

  a4→3 : alt₄ ≡ alt₃
  a4→3 = assoc p (q ∙ r) s

  a3→2 : alt₃ ≡ alt₂
  a3→2 = ap (_∙ s) (assoc p q r)

  -- Pentagon LHS: final → alt₁ → alt₂
  pent-lhs : final ≡ alt₂
  pent-lhs = a→1 ∙ a1→2

  pent-rhs : final ≡ alt₂
  pent-rhs = a→4 ∙ a4→3 ∙ a3→2

  HComposite₄-total : Type u
  HComposite₄-total = Σ c ∶ (v ≡ z) , (final ≡ c) × (c ≡ alt₂)

  -- pent-lhs and pent-rhs give sections of this space
  section-lhs : HComposite₄-total
  section-lhs = alt₂ , pent-lhs , refl

  section-rhs : HComposite₄-total
  section-rhs = alt₂ , pent-rhs , refl

  private
    fiber-at-alt₂ : Type u
    fiber-at-alt₂ = Σ eq ∶ (final ≡ alt₂) , alt₂ ≡ alt₂

    lhs-in-fiber : fiber-at-alt₂
    lhs-in-fiber = pent-lhs , refl

    rhs-in-fiber : fiber-at-alt₂
    rhs-in-fiber = pent-rhs , refl

qinvtofun : ∀ {u v} {A : Type u} {B : Type v} → Qinv A B → A → B
qinvtofun e = fst e
```

## Identity Type Characterizations

Characterizations of path types for sigma types, function types, and sum types.
These show that paths in structured types decompose into paths in their components.

```agda

open import Core.Equiv using (_≃_; iso→equiv; Equiv)

-- Sigma path characterization: a path in Σ B is a pair of a path in A and
-- a dependent path in B over it.
Σ-path-equiv
  : {A : Type u} {B : A → Type v} {w x : Σ B}
  → (w ≡ x) ≃ (Σ p ∶ (fst w ≡ fst x) , PathP (λ i → B (p i)) (snd w) (snd x))
Σ-path-equiv = iso→equiv fwd bwd sec retr
  where
  fwd : _
  fwd p = ap fst p , ap snd p

  bwd : _
  bwd (p , q) i = p i , q i

  sec : _
  sec _ = refl

  retr : _
  retr _ = refl

-- Π path characterization: funext as an equivalence.
-- Paths between functions are equivalent to pointwise paths.
Π-path-equiv
  : {A : Type u} {B : A → Type v} {f g : (x : A) → B x}
  → (f ≡ g) ≃ ((x : A) → f x ≡ g x)
Π-path-equiv = iso→equiv happly funext (λ _ → refl) (λ _ → refl)
```

### Sum type path characterizations

For sum types, paths between inl's are equivalent to paths between the
injected values, and similarly for inr's. Paths between inl and inr are
impossible (disjointness).

```agda

private
  -- Cover for sum types: decodes a path in A ⊎ B starting at inl a
  ⊎-codel : ∀ {u v} {A : Type u} {B : Type v} (a : A) → A ⊎ B → Type u
  ⊎-codel a (inl x) = a ≡ x
  ⊎-codel {u} a (inr _) = Lift u ⊥

  -- Cover for sum types: decodes a path in A ⊎ B starting at inr b
  ⊎-coder : ∀ {u v} {A : Type u} {B : Type v} (b : B) → A ⊎ B → Type v
  ⊎-coder {v = v} b (inl _) = Lift v ⊥
  ⊎-coder b (inr x) = b ≡ x

-- Path between inl's is equivalent to path between the values.
-- Credit: Standard encode-decode proof adapted from 1lab.
⊎-path-inl
  : {A : Type u} {B : Type v} {a a' : A}
  → (inl {B = B} a ≡ inl a') ≃ (a ≡ a')
⊎-path-inl {u} {v} {A = A} {B} {a} {a'} = iso→equiv fwd bwd sec retr
  where
  Code : A ⊎ B → Type u
  Code = ⊎-codel {B = B} a

  encode : (x : A ⊎ B) → inl a ≡ x → Code x
  encode x p = subst Code p refl

  decode : (x : A ⊎ B) → Code x → inl a ≡ x
  decode (inl x) q i = inl (q i)
  decode (inr _) (liftℓ ())

  fwd : inl a ≡ inl a' → a ≡ a'
  fwd = encode (inl a')

  bwd : a ≡ a' → inl a ≡ inl a'
  bwd = decode (inl a')

  -- sec: bwd (fwd p) ≡ p for p : inl a ≡ inl a'
  sec : (p : inl a ≡ inl a') → bwd (fwd p) ≡ p
  sec p = J {x = inl a}
            (λ (x : A ⊎ B) (q : inl a ≡ x) → decode x (encode x q) ≡ q)
            (ap (decode (inl a)) (transport-refl refl)) p

  -- retr: fwd (bwd p) ≡ p for p : a ≡ a'
  retr : (p : a ≡ a') → fwd (bwd p) ≡ p
  retr p = J (λ x (q : a ≡ x) → encode (inl x) (decode (inl x) q) ≡ q)
             (transport-refl refl) p

-- Path between inr's is equivalent to path between the values.
⊎-path-inr
  : {A : Type u} {B : Type v} {b b' : B}
  → (inr {A = A} b ≡ inr b') ≃ (b ≡ b')
⊎-path-inr {u} {v} {A = A} {B} {b} {b'} = iso→equiv fwd bwd sec retr
  where
  Code : A ⊎ B → Type v
  Code = ⊎-coder {A = A} b

  encode : (x : A ⊎ B) → inr b ≡ x → Code x
  encode x p = subst Code p refl

  decode : (x : A ⊎ B) → Code x → inr b ≡ x
  decode (inl _) (liftℓ ())
  decode (inr x) q i = inr (q i)

  fwd : inr b ≡ inr b' → b ≡ b'
  fwd = encode (inr b')

  bwd : b ≡ b' → inr b ≡ inr b'
  bwd = decode (inr b')

  -- sec: bwd (fwd p) ≡ p for p : inr b ≡ inr b'
  sec : (p : inr b ≡ inr b') → bwd (fwd p) ≡ p
  sec p = J {x = inr b}
            (λ (x : A ⊎ B) (q : inr b ≡ x) → decode x (encode x q) ≡ q)
            (ap (decode (inr b)) (transport-refl refl)) p

  -- retr: fwd (bwd p) ≡ p for p : b ≡ b'
  retr : (p : b ≡ b') → fwd (bwd p) ≡ p
  retr p = J (λ x (q : b ≡ x) → encode (inr x) (decode (inr x) q) ≡ q)
             (transport-refl refl) p

-- Disjointness: inl a and inr b are never equal
⊎-disjoint : {A : Type u} {B : Type v} {a : A} {b : B} → ¬ (inl a ≡ inr b)
⊎-disjoint p = subst discrim p tt
  where
  discrim : _ ⊎ _ → Type
  discrim (inl _) = ⊤
  discrim (inr _) = ⊥
