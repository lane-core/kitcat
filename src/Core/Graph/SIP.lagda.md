The Structure Identity Principle via reflexive graphs.

This module implements SIP using Sterling's framework: the universe of types
forms a univalent reflexive graph with equivalences as edges. Structures over
types are displayed reflexive graphs over this universe graph, and SIP follows
from univalence of the total space.

Reference: Sterling's reflexive graph lenses paper.

```agda

{-# OPTIONS --safe --cubical --no-guardedness --no-sized-types #-}
-- Note: This module uses --cubical (not --erased-cubical) because it requires
-- computational content from univalence (ua, Glue) which are erased in
-- --erased-cubical mode. This follows the precedent of Core.Univalence and
-- Core.Glue. Modules importing this can still use --erased-cubical.

module Core.Graph.SIP where

open import Core.Prelude
open import Core.Graph.Base
open import Core.Graph.Reflexive.Base
```

## The universe as a reflexive graph

The universe of types at level `u` forms a reflexive graph where:
- Vertices are types
- Edges are equivalences
- Reflexivity is the identity equivalence

```agda

Univ : ∀ u → Rx-graph (u ₊) u
Univ u .Rx-graph.graph .Graph.₀ = Type u
Univ u .Rx-graph.graph .Graph.₁ = _≃_
Univ u .Rx-graph.rx _ = equiv
```


## Univalence of Univ

A reflexive graph is univalent when its fans are propositional. For `Univ`,
this follows from the univalence axiom: the type `Sigma B : Type, A equiv B`
is contractible (hence propositional).

```agda

private
  module U {u} = rx-graph (Univ u)

-- The singleton type Σ B, A ≃ B is contractible
-- Adapted from 1lab's univalence proof; uses Glue types
equiv-singl-is-contr : ∀ {u} (A : Type u) → is-contr (Σ B ∶ Type u , A ≃ B)
equiv-singl-is-contr {u} A .center = A , equiv
equiv-singl-is-contr {u} A .paths (B , e) i = ua e i , eqv-over-ua i
  where
  open import Core.Glue

  -- Partial type-equiv pairs for the Glue boundaries
  Te : (j : I) → Partial (∂ j) (Σ T ∶ Type u , T ≃ B)
  Te j (j = i0) = A , e
  Te j (j = i1) = B , equiv

  -- The forward function path: id at j=i0, e.fst at j=i1
  fwd-path : PathP (λ j → A → ua e j) id (e .fst)
  fwd-path j a = glue {φ = ∂ j} {Te = Te j}
                      (λ { (j = i0) → a ; (j = i1) → e .fst a })
                      (inS (e .fst a))

  -- The equivalence path over ua e
  eqv-over-ua : PathP (λ j → A ≃ ua e j) equiv e
  eqv-over-ua j .fst = fwd-path j
  eqv-over-ua j .snd = is-prop→PathP (λ j → is-equiv-is-prop (fwd-path j))
                                      id-equiv (e .snd) j

-- The fan is propositional (immediate from contractibility)
Univ-is-univalent : ∀ {u} → U.is-univalent {u}
Univ-is-univalent {u} A = is-contr→is-prop (equiv-singl-is-contr A)
```


## Standard notion of structure

A standard notion of structure is a displayed reflexive graph over `Univ`.
This consists of:
- For each type `A`, a type of structures `S(A)`
- For each equivalence `e : A equiv B`, a relation between `S(A)` and `S(B)`
  expressing when the equivalence "preserves" the structure
- Reflexivity: the identity equivalence always preserves structure

```agda

-- Standard notion of structure at a given universe level
-- A structure is a displayed reflexive graph over Univ
import Core.Graph.Reflexive.Displayed as RxDisp

Standard-structure : ∀ u v → Type (u ₊ ⊔ v ₊)
Standard-structure u v = RxDisp.Disp-rx-graph (Univ u) v v

module Std-str {u v} (S : Standard-structure u v) where
  private
    -- Open the parameterized displayed module at Univ u
    module DispMod = RxDisp (Univ u)
    -- Open the record S
    open DispMod.Disp-rx-graph S

  -- The type of structures over a type
  Str : Type u → Type v
  Str = Ob

  -- When an equivalence preserves structure
  _preserves_ : ∀ {A B} → A ≃ B → Str A → Str B → Type v
  _preserves_ {A} {B} e s t = ₂ {A} {B} e s t

  -- Identity preserves structure
  id-preserves : ∀ {A} (s : Str A) → _preserves_ {A} {A} equiv s s
  id-preserves {A} s = rx A s
```


## Total space

The total space of a structure is the type of pairs `(A, s)` where `A` is a
type and `s : S(A)` is a structure on it.

```agda

  Total : Type (u ₊ ⊔ v)
  Total = Σ A ∶ Type u , Str A

  -- Equivalences in the total space: an equivalence of types that preserves structure
  Total-equiv : Total → Total → Type (u ⊔ v)
  Total-equiv (A , s) (B , t) = Σ e ∶ (A ≃ B) , _preserves_ e s t
```


## SIP: paths in the total space

The Structure Identity Principle: if the displayed graph is univalent
(i.e., for each equivalence there's a unique structure transport), then
paths in the total space are equivalent to structure-preserving equivalences.

```agda

  -- Displayed fan: structures over B together with a preservation witness
  Str-fan : ∀ {A B} → A ≃ B → Str A → Type v
  Str-fan {B = B} e s = Σ t ∶ Str B , _preserves_ e s t

  -- The structure is univalent when displayed fans are contractible
  is-univalent-str : Type (u ₊ ⊔ v)
  is-univalent-str = ∀ {A B} (e : A ≃ B) (s : Str A) → is-contr (Str-fan e s)

  module SIP (str-univ : is-univalent-str) where
    -- Transport of structure along an equivalence
    str-transport : ∀ {A B} → A ≃ B → Str A → Str B
    str-transport e s = str-univ e s .center .fst

    -- The preservation witness
    str-transport-preserves : ∀ {A B} (e : A ≃ B) (s : Str A)
                            → _preserves_ e s (str-transport e s)
    str-transport-preserves e s = str-univ e s .center .snd

    -- Identity transport is identity
    str-transport-id : ∀ {A} (s : Str A) → str-transport equiv s ≡ s
    str-transport-id {A} s = ap fst (str-univ equiv s .paths (s , id-preserves s))

    -- Uniqueness of transported structure
    str-transport-unique : ∀ {A B} (e : A ≃ B) (s : Str A) (t : Str B)
                         → _preserves_ e s t → str-transport e s ≡ t
    str-transport-unique e s t p = ap fst (str-univ e s .paths (t , p))

    -- Note: The full SIP equivalence (Total-equiv X Y ≃ (X ≡ Y)) requires
    -- additional universe polymorphism in _preserves_ to handle the inverse
    -- direction properly. For now we provide the key transport operations.
```


## Example: Magma structures

A magma is a type with a binary operation. We show this forms a univalent
displayed graph over Univ, demonstrating SIP in action.

```agda

module Magma-example where
  -- Magma structure: a binary operation
  Magma-str : ∀ {u} → Type u → Type u
  Magma-str A = A → A → A

  -- When an equivalence preserves magma structure:
  -- The equivalence is a homomorphism: e (m x y) ≡ n (e x) (e y)
  _preserves-magma_ : ∀ {u} {A B : Type u} → A ≃ B → Magma-str A → Magma-str B → Type u
  _preserves-magma_ {A = A} {B} e m n =
    ∀ (x y : A) → e .fst (m x y) ≡ n (e .fst x) (e .fst y)

  -- The displayed reflexive graph of magma structures
  Magma-disp : ∀ u → Standard-structure u u
  Magma-disp u = record
    { disp = record { Ob = Magma-str ; ₂ = _preserves-magma_ }
    ; rx = λ A m x y → refl
    }

  -- Magma structure is univalent when the carrier is a set
  -- This is the standard assumption for algebraic structures in HoTT
  -- Given e : A ≃ B and m : Magma-str A, there's a unique n : Magma-str B
  -- such that e preserves m n
  Magma-is-univalent : ∀ {u} {A B : Type u} → is-set B
                     → (e : A ≃ B) (m : Magma-str A)
                     → is-contr (Σ n ∶ Magma-str B , _preserves-magma_ e m n)
  Magma-is-univalent {u} {A} {B} Bset e m = contr
    where
    -- The transported structure: n x y = e (m (e⁻¹ x) (e⁻¹ y))
    n : Magma-str B
    n x y = e .fst (m (Equiv.inv e x) (Equiv.inv e y))

    -- Proof that e preserves m n
    pres : _preserves-magma_ e m n
    pres x y =
      e .fst (m x y)
        ≡⟨ ap (λ z → e .fst (m z y)) (sym (Equiv.unit e x)) ⟩
      e .fst (m (Equiv.inv e (e .fst x)) y)
        ≡⟨ ap (λ z → e .fst (m (Equiv.inv e (e .fst x)) z)) (sym (Equiv.unit e y)) ⟩
      e .fst (m (Equiv.inv e (e .fst x)) (Equiv.inv e (e .fst y)))
        ≡⟨ refl ⟩
      n (e .fst x) (e .fst y) ∎

    -- Preservation proofs are propositional because B is a set
    pres-is-prop : (n'' : Magma-str B) → is-prop (_preserves-magma_ e m n'')
    pres-is-prop n'' f g = funext λ x → funext λ y →
      Bset (e .fst (m x y)) (n'' (e .fst x) (e .fst y)) (f x y) (g x y)

    -- Uniqueness: any other (n', p') equals (n, pres)
    unique : (fan : Σ n' ∶ Magma-str B , _preserves-magma_ e m n') → (n , pres) ≡ fan
    unique (n' , p') = Σ-prop-path pres-is-prop fst-eq
      where
      fst-eq : n ≡ n'
      fst-eq = funext λ x → funext λ y →
        n x y
          ≡⟨ ap (λ z → e .fst (m z (Equiv.inv e y)))
               (ap (Equiv.inv e) (sym (Equiv.counit e x)) ∙ Equiv.unit e _) ⟩
        e .fst (m (Equiv.inv e x) (Equiv.inv e y))
          ≡⟨ p' (Equiv.inv e x) (Equiv.inv e y) ⟩
        n' (e .fst (Equiv.inv e x)) (e .fst (Equiv.inv e y))
          ≡⟨ ap2 n' (Equiv.counit e x) (Equiv.counit e y) ⟩
        n' x y ∎

    contr : is-contr (Σ n' ∶ Magma-str B , _preserves-magma_ e m n')
    contr .center = n , pres
    contr .paths = unique

  -- Bundled magma type
  Magma : ∀ u → Type (u ₊)
  Magma u = Std-str.Total (Magma-disp u)

  -- Note: To apply Std-str.SIP, one would need to show that Magma-is-univalent
  -- holds for all A B e m. This requires either:
  -- 1. Restricting to set-based magmas (most common in practice)
  -- 2. Using a modified structure definition with propositional preservation
  --
  -- Example usage with set assumption:
  -- module Magma-SIP-Set {u} (Aset : (A : Type u) → is-set A) where
  --   univ : Std-str.is-univalent-str (Magma-disp u)
  --   univ e m = Magma-is-univalent (equiv→is-hlevel 2 e (Aset _)) e m

```
