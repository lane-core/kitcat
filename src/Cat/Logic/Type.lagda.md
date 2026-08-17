---
author: Lane Biocini
date: 2026-07-08
last-modified: 2026-07-13
---

Virtual graph theory aims to provide a higher-dimensional setting for
the methods of categorical logic. It is influenced especially by
Sterling's work on reflexive graph lenses and his formalization of
duploids, by Shulman's notion of deductive system, and by the methods
of virtual double category theory. Its basic methodological principle
is that composition and structural operations should not be taken as
primitive operations on arrows, but should arise as representability
phenomena for contextual actions.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Type where

open import Core.Type
open import Core.Base

open import Core.Data.Sigma
open import Core.Path.Base
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding using (is-embedding)
open import Core.Equiv.Properties using (has-section)
```

A virtual graph begins with the data of a directed graph, or quiver.
We read objects as formulae and each type `hom x y` as a sequent, whose
inhabitants are its derivations.

```agda
record virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob : Type o
    hom : ob → ob → Type h
```

To state the remainder requires us to establish elementary notation.

We interpret the arrows into and out of an object as terms and coterms.
A term based at `x` presents an edge whose target is `x`, while a
coterm based at `y` presents an edge whose source is `y`.


```agda
  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v
```

These types are respectively the co-fan and fan of an object in the
terminology of Sterling's theory of reflexive graphs. For a univalent
reflexive graph, each is contractible with center given by the object
together with its reflexivity edge. Here we do not impose this
condition on the underlying graph; instead, the two fan constructions
are retained as the two sides of the contexts on which judgments act.

Confronting a term based at x with a coterm based at y produces a
two-sided context with a distinguished gap from x to y.

   `w → x  | ? |  y → z`

We call such a pair an argument.

```agda
  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y
```

The outer boundary of an argument is determined by the antecedent of
its term and the succedent of its coterm.

```agda
  ant : ∀ {x y} → argument x y → ob
  ant = fst ∘ fst

  scd : ∀ {x y} → argument x y → ob
  scd = fst ∘ snd
```

A conclusion for an argument is an edge closing this outer
boundary.

```agda
  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (ant γ) (scd γ)
```

We may now define the central notion, the Π counterpart of the Σ type
above. A judgment from x to y is a uniform two-sided action on
contexts having a distinguished gap from `x` to `y`.

```agda
  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ
```

Thus, if we have `φ : judgment x y` and edges:

  `f : hom w x` and `g : hom y z`

then we may derive the conclusion:

  `φ ((w , f) , (z , g)) : hom w z`

Finally, every derivation from x to y is required to determine such
a contextual action.

```agda
  field
    reflect : ∀ {x y} → hom x y → judgment x y
```

Reflection therefore expresses the principle that an edge may be
displayed uniformly in every two-sided context having the appropriate
gap.

There is also a geometric resemblance between the resulting two-sided
notion of contextual action and Sterling's unbiased dependent lenses,
in which a family indexed by an edge receives coercions from
independent left-hand and right-hand diagonal components into a common
centre. The constructions are different: here the two sides are a
co-fan and fan forming the context of a judgment. Nevertheless, both
make essentially two-sided boundary data explicit rather than reducing
it in advance to a single variance.

```agda
module sequents {o h} (G : virtual-graph o h) where
  open virtual-graph G
```

A gloss is in order before we continue.

The above may seem unnecessarily elaborate. One might object:
'judgment' only has the shape of a hardcoded composition function
pinned at the target and source of two edges (i.e. term and coterm)
which one would ordinarily regard as presenting an ordinary notion of
ternary composition if we were in a category. So why all the fuss?

Allow me to motivate this peculiar construction, for this style of
presentation arose after considering the basic notion of composition
from multiple points of view.

In one style of formal treatment we might portray matters like this:
given two edges `f, g`, they are compatible when the target of `f`
matches the source of `g`, allowing us to form the composition `f ⨾ g`.

If we had a non-dependent type of edges and a separate sort of
objects, where edges are defined as a span with two projections `source`
and `target` of type `hom → ob`, we would describe this condition as
`target(f) ≡ source(g)`. While cumbersome for the purpose of
formalization, this presentation has the advantage of being explicit
about what it assumes in context; given, schematically, a
compatibility derivation in a surrounding two-sided context

  `Γ, f, g ⊢ target(f) ≡ source(g), Δ`,

we can regard composition as an operation which consumes this
derivation together with the two independently presented edges,
yielding the composite of `f` and `g`.

If compatibility is witnessed by an identity, then the witness need
not in general be unique: for fixed objects x and y, the type x ≡ y
may itself carry higher structure. Nevertheless, identity types
organize these witnesses canonically relative to reflexivity. For
every `x`, the total space

  `Σ y : ob , x ≡ y`

is contractible, with center `(x , refl)`.

This observation becomes relevant when we compare the preceding
presentation with the conventional dependent presentation of
composition:

  `_⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z`

On purely syntactic grounds we might naively suppose that we are on
sound footing: source and target match on the nose. Here the two
middle boundaries are not independently presented and subsequently
shown to be compatible: they are given from the outset by the very
same index `y`. The ordinary dependent signature does not express that
the two boundaries have been compared and found compatible. Rather, it
prevents them from ever being presented separately. Compatibility has
been strictified into the indexing discipline of the type itself.

To expose that datum we may instead write something of the form:

  `_⨾[_]⨾_ : ∀ {w x y z} → hom w x → x ≡ y → hom y z → hom w z`

in which the two boundaries x and y are independently presented and a
witness of their compatibility is supplied explicitly. Identity
provides one possible notion of such compatibility, coherently
organized around reflexivity by the contractibility of the singleton
above.

The lesson we retain is not that compatibility must itself be an
identity type, but that the data involved in compatibility should not
be strictified away by the notation of a common boundary. The
construction of `judgment` is designed to preserve the corresponding
separation between contextual presentation and mediation. A term and
coterm independently present the two sides of a context, leaving a
distinguished gap from x to y; a judgment specifies a uniform action
through that gap without identifying the action itself with an
edge. Reflection then records how an actual derivation occupying the
gap acts in every such surrounding context.

The case of the identity type is instructive, however, because it
directs us to consider the special contextual action obtained by
reflecting an edge capable of serving as a unit. Indeed, we will go on
to show that if, for every `x`, we have an edge

  `idn x : hom x x`

satisfying the analogue, in our setting, of Kraus and Capriotti's notion
of idempotent equivalence, then

  `reflect (idn x) : judgment x x`

corresponds exactly to the expected notion of categorical composition:
composition is recovered as the contextual action of the unit. What is
this action? Informally, the unit does nothing to the way precomposite
and postcomposite meet; it simply closes the gap between them. In a
sense we will make literal, the unit can be said to reify the
surrounding context that renders their encounter coherent, where their
ability to meet is premised on this datum, the unit, which formally
represents the legibility of their encounter. The resulting
notion of composition will moreover carry higher coherences, such as
the pentagon and its higher analogues, arising from the same
representability principle.

This picture has a close analogue in virtual double category theory.
There, units are nullary composites, while ordinary loose composites
are higher-arity instances of the same representability phenomenon; a
virtual double category in which all horizontal composites and units
exist is equivalently a pseudo double category.

Returning to our concrete presentation, we would have:

```text
  f : hom w x
  g : hom x v

  f ⨾ g : hom w v
  f ⨾ g = reflect (idn x) ((w , f) , (v , g))
```

The same ambient notion of judgment, however, admits representability
principles more general than unital composition; we will show that cut
arises in this way.

For now, we can record an elementary but conceptually useful fact
which clarifies the relation between edges and judgments.

Define the fibers of reflect to be the witnesses that a judgment is
represented by an edge, together with the canonical representation
witness of every reflected edge:

```agda
  is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-representable = fiber reflect

  normal : ∀ {x y} (f : hom x y) → is-representable (reflect f)
  normal f = f , refl
```

The following equivalence then has an immediate interpretation:

```
  hom≃total-representable
    : ∀ {x y} → hom x y ≃ (Σ α ∶ judgment x y , is-representable α)
  hom≃total-representable {x} {y} = iso→equiv fwd bwd hom-ret rep-sec
    where
      fwd : hom x y → Σ F ∶ judgment x y , is-representable F
      fwd f = reflect f , (f , refl)

      bwd : (Σ α ∶ judgment x y , is-representable α) → hom x y
      bwd (_ , a , _) = a

      hom-ret : ∀ f → bwd (fwd f) ≡ f
      hom-ret f = refl

      rep-sec : ∀ s → fwd (bwd s) ≡ s
      rep-sec (_ , a , p) = J (λ F' p' → fwd a ≡ (F' , a , p')) refl p
```

Formally, this is the familiar equivalence between the domain of a map
and the total space of its fibers. Here it admits a useful reading: an
edge from `x` to `y` is equivalently a judgment from `x` to `y`
together with a chosen representation of that judgment by an edge.

This does not assert that every judgment is representable. Rather, the
subsequent structure carried by a virtual graph will be expressed by
requiring particular contextual actions to admit canonical, typically
contractibly determined, representatives, particularly those expressed
over various kinds of total spaces.

In this spirit, we will now define the type of deductions which are
possibly spurious in nature (no link between the argument and the
supposed conclusion).

```agda
  deduction : ob → ob → Type (o ⊔ h)
  deduction x y = Σ γ ∶ argument x y , conclusion γ

  module deduction {x y} (d : deduction x y) where
    private
      γ = d .fst
      c = d .snd
```

We regard that we have a viable solution when we possess some
edge which can show that that way to fill the hole has a definite
relation to the conclusion: it is not spurious. We demonstrate that a
deduction is genuinely a solution by showing that there is a way to
relate the specific conclusion to the canonical judgment given by
reflect.

```agda
    solution : Type h
    solution = Σ d ∶ hom x y , c ≡ reflect d γ

    conclude : solution → Σ s ∶ conclusion γ , c ≡ s
    conclude (d , p) = reflect d γ , p
```

Observe that we have a pullback square for this fixed argument and solution.

                    conclude
   solution  ───────────────────────>  Singl c
       │                                  │
       │                                  │
   fst │                                  │ fst
       │                                  │
       ▼                                  ▼
    hom x y  ───────────────────────>  conclusion γ
               λ s → reflect s γ

And furthermore that we can now formulate a hierarchy of coherence
properties of interest, namely that the space of solutions satisfies
various conditions related to lifts.

```agda
    has-answer : Type h
    has-answer = has-section conclude

    is-determinate : Type h
    is-determinate = is-embedding conclude

    is-solvable : Type h
    is-solvable = is-equiv conclude

  vcell
    : ∀ {x y}
    → ((u , t) : term x)
    → judgment x y
    → ((v , c) : coterm y)
    → hom u v
    → Type h
  vcell Γ α Δ c = c ≡ α (Γ , Δ)

  is-opcartesian : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-opcartesian {x} {y} α =
    (d : deduction x y) (q : d .snd ≡ α (d .fst))
      → is-contr (fiber (deduction.conclude d) (α (d .fst) , q))

```

To conclude this module I offer the following final comments.

A `deduction X Y` fixes the following problem: what is the way we can
reason with Γ ⊢ X, X ⊢ Y, and Y ⊢ Δ such that we obtain, in the end,
some Γ ⊢ Δ (the shape of a "conclusion" edge), which agrees with a
coherent notion of cut. Notice that our formalism does not opine on
the decision of which cut happens first in the casual sense: the cut
of Γ ⊢ X and X ⊢ Y; or the cut of X ⊢ Y and Y ⊢ Δ; indeed this is
essential for allowing a decisive area of concern to enter into our
developing subject, matters such as Lafont's critical pair, which make
the coherence of cut a subtle matter.

In general this coherence ought to concern how the way of completing
arguments using cut has some definite relationship to the shape of how
things can be concluded in general. In other words, that cut
elimination obtains for a candidate logical framework can be
interpreted as the demand that for each proof using cut, there is some
deduction which is not spuriously related to this means of deduction.
If we can deduce something using cut, the cut-free deduction denoting
it necessarily obtains, and both the procedure and the denotation are
determined in mutual fashion.

The matter of cut elimination is more subtle than "cut is unnecessary,
the cut-free proof is canonical and the only one that truly
matters". The subtlety comes from fixing how it comes to be that it
matters, and this has precisely to do with how we can define an
irrelevant procedure that coincides with it. Indeed, it is well known
that a system is consistent, and hence only becomes relevant as a
system of reasoning at all, once we are able to do precisely this
thing: eliminate the cut. Philosophically speaking, we can say that
what's at stake in forging a system of reasoning is not a procedure
for defining what truth is, but how to forget everything except the
truth, and to further observe that there is quite a lot that can be
forgotten. In fact some part of the truth must disappear as well,
otherwise the whole enterprise is lost.
