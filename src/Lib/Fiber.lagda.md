Lane Biocini
Sept 17th, 2024

I realized that a type I had many proprerties worked out for already was quite
suitable to serve as our Fiber type. In particular, it is an identity system.

```agda

{-# OPTIONS --safe  #-}

module Lib.Fiber where

open import Lib.Prim
open import Lib.Typoid

```

This is the type of fiber bundles; projections from a base space given by B,
where the term of our dependent type family is a projection function applied on
the point `e : E`. The path leading towards `e` is given by the action of
`f : Π B`, and this function applied to a term `e : E` produces a term `f e : B e`
corresponding to the point in the base space that is reached by the path. To
have this `f` entails that this definition induces a type family recording all such
paths reachable with any `f`; it is in this sense we call this type a Bundle.

This term `f e` comprises not only an instance of a point of the base space,
but also a proof of the path required to reach it from our space `E`. As such,
this proof has an elimination principle, which is that for each point in the
base space we can produce the corresponding point that is projected in E.

```
module _ {u v} {E : u type} where
 data Bundle (B : E → v type) (f : Π B) : (e : E) → B e → u ⊔ v type where
  path : (e : E) → Bundle B f e (f e)

 module _ {B : E → v type} {f : Π B} {e : E} {x : B e} where
  pt : Bundle B f e x → E
  pt = λ _ → e

  proj : (f : Π B) (e : E) → Bundle B f e (f e)
  proj f = path

```

We can define our type's notion of induction and transport typd-straightaway

```
 ind : ∀ {w} {B : E → v type} {f : Π B} {e : E}
     → (P : (y : B e) → Bundle B f e y → w type)
     → P (f e) (path e)
     → (b : B e) (q : Bundle B f e b)
     → P b q
 ind P p b (path ._) = p


 trb : ∀ {w} {B : E → v type} {e : E} (P : B e → w type)
     → {b : B e} {f : Π B} → Bundle B f e b
     → P (f e) → P b
 trb P {b} q p = ind (λ y _ → P y) p b q


```

Computation rules

```
ind-htpy-β : ∀ {u v w} {E : u type} (B : E → v type) {e : E} {f : Π B}
      → (P : (y : B e) → Bundle B f e y → w type)
      → (p : P (f e) (path e))
      → Bundle (P (f e)) (ind P p (f e)) (path e) p
ind-htpy-β B {e} P p = path (path e)

ind-β : ∀ {u v} {E : u type} (B : E → v type) {e : E} {f : Π B}
      → Bundle B (λ - → ind (λ y _ → B y) (f -) - (path e)) e (f e)
ind-β B {e} = path e

```

Application on paths is a bit weird here. What we need to do is lay out a function
such that the following fibers commute:

                  f
    x : E --------------------> b : B x
      |                           |
      |                           |
      |                           |
   h  |                           | g
      |                           |
      |                           |
      |                           |
      v                           v
 t : D x (f x) ............... g b : D x b

Unfortunately, we run into problems even at the formation rule, because `f x` is not
judgmentally equal to b and the fibered nature of this square entails that we run
into the same problem that we have in ordinary ap, i.e. we cannot apply a Pi type
to an equality. What can actually be done is to transport along the dotted line, which
is the term 't'. We give a function apb with this definition.

But it it also possible to consider: what is the function that would give our 'h'?
So we also consider that we can lift a square in the opposite category, so that we
obtain a function that can transport any fiber along g between a `B x` and `D x b`;
in other words, this composes the function like the S-combinator.

```

apb : ∀ {u v w} {E : u type} {B : E → v type} {D : (x : E) → B x → w type}
    → (f : Π B) (g : (x : E) → (a : B x) → D x a)
    → {e : E} {b : B e} (p : Bundle B f e b)
    → Bundle (D e) (g e) b (trb (D e) p (g e (f e)))
apb f g (path _) = path (f _)

aps : ∀ {u v w} {E : u type} {B : E → v type} {D : (x : E) → B x → w type}
      → (f : Π B) (g : (x : E) → (a : B x) → D x a)
      → {e : E} {b : B e} {c : D e (f e)}
      → (p : Bundle (D e) (g e) (f e) c)
      → Bundle (λ - → D - (f -)) (λ - → g - (f -)) e c
aps f g {e} (path .(f e)) = path e

```

Notice that Bundle gives a definition of CoYoneda as the non-dependent form
(with inputs switched).

> data CoYoneda f a = forall b. CoYoneda (b -> a) (f b)
> -- from https://gist.github.com/gregberns/ede18190d5117eea6fb51815e2eab9b2

We give the interpretation of CoYoneda presented here in the fibrational model of
dependent types as follows:

CoYoneda defined for a function `f : E → B` on `a : B` of some base space `B`
is a proof that for any `b : E` of a space E, we have a typd-structure encoding the
type of computations performed on the point `a` by f, such that we can show that
our chosen `a` is actually given by some `f b : B`; as such, CoYoneda is the
fiber over a point a. It satisfies the properties of the CoYoneda type because
as a type its inhabitants capture the necessary instances generating the possible
computations given by a function f, thus one may program utilizing objects computed
by programs `f (g (h (...)))` in advance of this computation. as the typd-structure of
path composition is given by the rewrites applied by the application of f, g, h, and
so on.

```

CoYoneda : ∀ {u v} {E : u type} {B : v type} → (E → B) → B → E → v type
CoYoneda {u} {v} {E} {B} f a = Bundle (λ _ → B) id a ∘ f

apc : ∀ {u v w} {E : u type} {B : v type} {D : w type}
    → (f : E → B) (g : B → D)
    → {e : E} {b : B} → CoYoneda f b e
    → CoYoneda g (g b) (f e)
apc f g (path .(f _)) = path (g (f _))
