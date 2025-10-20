Lane Biocini

Sept 17th, 2024 (edited Oct 2025)

```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Coyo where

open import Prim.Type renaming (funcomp to infixr 40 _∘_)
open import Prim.Data.Sigma

infix 0 _＝_
```
This defines a singleton type construction that witnesses when a point lies in
the image of a function. For a function `f : Π B` and base point `e : E`,
`Bundle B f e x` is inhabited precisely when `x = f e`.

While I call this "Bundle" due to its projection structure, it's more precisely
a family of contractible types.

This construction yields (an interpretation of) CoYoneda lemma and path types as
special cases.
```agda
data Bundle {u v} {E : Type u} (B : E → Type v) (f : Π B) : (e : E) → B e → Type (u ⊔ v) where
  path : (e : E) → Bundle B f e (f e)

module _ {u v} {E : Type u} {B : E → Type v} {f : Π B} {e : E} {x : B e} where
  pt : Bundle B f e x → E
  pt = λ _ → e

  proj : (f : Π B) (e : E) → Bundle B f e (f e)
  proj f = path
```
We can define our type's notion of induction and transport straightaway
```agda
module _ {u v} {E : Type u} where
  ind : ∀ {w} {B : E → Type v} {f : Π B} {e : E}
      → (P : (y : B e) → Bundle B f e y → Type w)
      → P (f e) (path e)
      → (b : B e) (q : Bundle B f e b)
      → P b q
  ind P p b (path ._) = p

  trb : ∀ {w} {B : E → Type v} {e : E} (P : B e → Type w)
      → {b : B e} {f : Π B} → Bundle B f e b
      → P (f e) → P b
  trb P {b} q p = ind (λ y _ → P y) p b q
```
Computation rules
```agda
ind-htpy-β : ∀ {u v w} {E : Type u} (B : E → Type v) {e : E} {f : Π B}
      → (P : (y : B e) → Bundle B f e y → Type w)
      → (p : P (f e) (path e))
      → Bundle (P (f e)) (ind P p (f e)) (path e) p
ind-htpy-β B {e} P p = path (path e)

ind-β : ∀ {u v} {E : Type u} (B : E → Type v) {e : E} {f : Π B}
      → Bundle B (λ - → ind (λ y z → B -) (f -) - (path e)) e (f e)
ind-β B {e} = path e
```
Action on paths is a bit weird here. Given:
- `f : Π B`  (selecting a point in each fiber)
- `g : (x : E) → (a : B x) → D x a`  (a fiberwise function)
what we need to do is lay out a function such that the following diagram commutes:
```
--                  f
--     x : E --------------------> b : B x
--       |                           |
--       |                           |
--       |                           |
--    h  |                           | g
--       |                           |
--       |                           |
--       |                           |
--       v                           v
--  t : D x (f x) ............... g b : D x b
```
We want to compose these along Bundle paths, but face a typing challenge:
for arbitrary `b : B e`, we cannot directly apply g because `f e` and `b`
are not judgmentally equal.

The functions apb and aps provide two solutions:
- apb: transports forward from D e (f e) to D e b
- aps: lifts backward from the fiber over f e to compose with f
```agda
apb : ∀ {u v w} {E : Type u} {B : E → Type v} {D : (x : E) → B x → Type w}
    → (f : Π B) (g : (x : E) → (a : B x) → D x a)
    → {e : E} {b : B e} (p : Bundle B f e b)
    → Bundle (D e) (g e) b (trb (D e) p (g e (f e)))
apb f g (path _) = path (f _)

aps : ∀ {u v w} {E : Type u} {B : E → Type v} {D : (x : E) → B x → Type w}
      → (f : Π B) (g : (x : E) → (a : B x) → D x a)
      → {e : E} {b : B e} {c : D e (f e)}
      → (p : Bundle (D e) (g e) (f e) c)
      → Bundle (λ - → D - (f -)) (λ - → g - (f -)) e c
aps f g {e} (path .(f e)) = path e
```
The profunctor CoYoneda lemma states:
  P(A,B) ≅ ∫^C Hom(C,A) × P(C,B)

In our dependent type setting:
- Bundle B f plays the role of a dependent profunctor
- The coend becomes existential quantification
- For the special case P(e,b) = (f e = b), we get:

  (f e = b) ≅ ∃(e' : E). (e' = e) × (f e' = b)

Bundle internalizes this by making path e the witness.

The general profunctor P gives P(e,b) for arbitrary relations.
We specialize to the "graph" profunctor: P(e,b) = (f e = b)
This recovers the fiber/preimage structure.
```agda
CoYoneda : ∀ {u v} {E : Type u} {B : Type v} → (E → B) → B → E → Type v
CoYoneda {u} {v} {E} {B} f a b = Bundle (const B) id a (f b)
```
This type is inhabited (by `path (f e)`) precisely when `f e ≡ a`.

In categorical terms, CoYoneda f represents the presheaf sending each `a : B`
to its preimage under f. The type `CoYoneda f a` collects witnesses that `a`
lies in the image of `f`, packaged with the source point.

This satisfies the CoYoneda property: we can "pre-compose" morphisms before
actually computing them, as shown by the `apc` function.
```agda
apc : ∀ {u v w} {E : Type u} {B : Type v} {D : Type w}
    → (f : E → B) (g : B → D)
    → {e : E} {b : B} → CoYoneda f b e
    → CoYoneda g (g b) (f e)
apc f g (path .(f _)) = path (g (f _))
```
Setting f = id recovers path types:
```agda
Path : ∀ {u} {A : Type u} → A → A → Type u
Path = CoYoneda id
_＝_ = Path
```
This has an inhabitant `path b : Path b b` when `a = b`, giving us reflexivity.
The path induction principle follows directly from Bundle's ind.

This reveals paths as the special case of CoYoneda where we ask:
"what is the preimage of b under the identity function?"
```agda
module _ {u} {A : Type u} where
 refl : {a : A} → Path a a
 refl {a} = path a
```
This version of path induction computes definitionally on path constructors,
as expected for a well-behaved path type.
```agda
path-induction : ∀ {u v} {A : Type u} {a : A}
               → (P : (x : A) → Path a x → Type v)
               → (x : A) (q : a ＝ x) → P a refl → P x q
path-induction P x (path .x) = id

tr : ∀ {u v} {A : Type u} (P : A → Type v) → {x y : A} → x ＝ y → P x → P y
tr P {x} {y} p a = path-induction (λ - _ → P -) y p a

ap : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
ap {u} {v} {A} {B} f {x} {y} p = apc id f p
```
`Bundle B f` exhibits a type-theoretic analogue of left Kan extension:
it witnesses when `b : B e` lies in the image of the section `f : Π B`,
giving us the dependent version of the CoYoneda lemma.

More precisely: where category theory has functors between categories,
we have type families over types; where it has natural transformations,
we have dependent functions (sections); and `Bundle B f e b` witnesses the
universal property that characterizes the Kan extension at component `(e,b)`.

In category theory: Given `f: C → D` and `B: C → E`,
`Lan_f(B)` is characterized by: For any functor `G: D → E`,
  `Nat(Lan_f(B), G) ≅ Nat(B, G∘f)`
where these are natural transformation sets in `[D,E]` and `[C,E]` respectively

In our type theory: Bundle satisfies the analogous property:
  `((e : E) (b : B e) → Bundle B f e b → D e b) ≅ ((e : E) → D e (f e))`
i.e., sections of D over Bundle ≅ sections of D along the graph of f
```agda
-- Bundle B f is universal among dependent types that factor through f
universal : ∀ {u v w} {E : Type u} {B : E → Type v}
          → (D : (e : E) → B e → Type w)
          → {f : Π B} → ((e : E) → D e (f e))
          → ((e : E) (b : B e) → Bundle B f e b → D e b)
universal D g e b p = trb (D e) p (g e)
```
The CoYoneda isomorphism for Bundle:

For any D : (e : E) → B e → Type, we have:
  `((e : E) → D e (f e)) ≅ ((e : E) (b : B e) → Bundle B f e b → D e b)`
```agda
module _ {u v w} {E : Type u} {B : E → Type v} (D : (e : E) → B e → Type w) (f : Π B) where
  to : ((e : E) → D e (f e)) → ((e : E) (b : B e) → Bundle B f e b → D e b)
  to = universal D

  from : ((e : E) (b : B e) → Bundle B f e b → D e b) → ((e : E) → D e (f e))
  from h e = h e (f e) (path e)

  iso₁ : (g : (e : E) → D e (f e)) → from (to g) ＝ g
  iso₁ g = refl -- definitional

  -- this part needs funext
  module _ (fe : ∀ {u v} {A : Type u} {B : A → Type v} {f g : Π B} → ((x : A) → f x ＝ g x) → f ＝ g) where
    iso₂ : (h : (e : E) (b : B e) → Bundle B f e b → D e b) → to (from h) ＝ h
    iso₂ h = fe λ e → fe λ b → fe λ p → ind (λ b p → to (from h) e b p ＝ h e b p) refl b p
