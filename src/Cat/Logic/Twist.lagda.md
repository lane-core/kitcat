---
author: Lane Biocini
date: 2026-08-10
---

We define the various notions of twist, leaning on Selinger's extended
abstract _Autonomous categories in which A ≅ A*_. It is also appropriate,
to restate here that virtual graph theory takes influence from Sterling's
treatment of Categorical Logic in his formalization of Duploid theory,
a major decision of which proceeded based on an informal remark he received
from Munch-Maccagnoni, cited from [TypeTopology](https://martinescardo.github.io/TypeTopology/
Duploids.DeductiveSystem.html):

```text
 module _ {A B : ob} (f : A ⊢ B) where
  is-thunkable : 𝓤 ⊔ 𝓥 ̇
  is-thunkable =
   (C D : ob) (g : B ⊢ C) (h : C ⊢ D)
   → cut (cut f g) h ＝ cut f (cut g h)

  is-linear : 𝓤 ⊔ 𝓥 ̇
  is-linear =
   (U V : ob) (g : V ⊢ A) (h : U ⊢ V)
   → cut (cut h g) f ＝ (cut h (cut g f))

 module _ (A : ob) where
  is-positive : 𝓤 ⊔ 𝓥 ̇
  is-positive =
   (B : ob) (f : A ⊢ B)
   → is-linear f

  is-negative : 𝓤 ⊔ 𝓥 ̇
  is-negative =
   (B : ob) (f : B ⊢ A)
   → is-thunkable f
```

Instead of axiomatizing an explicit polarity operator on objects, one
characterizes the objects by their extensional behavior on associators.
Polarized objects are therefore formalized by the total space of linear
and thunkable associators on an object.

```text
Pos : Type
Pos = Σ a ∶ ob, is-positive a
             -- ---------------
             -- (a : ob) (f : hom a b) → is-linear f
             -- --------------------------------------
             -- (a : ob) (f : hom a b) (u v : ob)
             -- (g : hom v a) (h : hom u v)
             --    → cut (cut h g) f ≡ (cut h (cut g f))

Neg : Type
Neg = Σ a ∶ ob, is-negative a
             -- ---------------
             -- (b : ob) (f : hom b a) → is-thunkable f
             -- -----------------------------------------
             -- (b : ob) (f : hom b a) (c d : ob)
             -- (g : hom b c) (h : hom c d)
             --    → cut (cut f g) h ≡ (cut f (cut g h))
```

It must be acknowledged where that puts us with regard to Selinger:
proceeding this way entails that we are formalizing a strict notion of
duality structure where the type of objects is uniform and we merely
locate polarization within it.

This entails a key methodological consideration we must heed when we
read Selinger: whenever we see a morphism like `h : hom x (x*)` (for
the half-twist) this must be interpreted by a morphism which maps
positive to negative objects and vice versa when it is inhabitable,
accompanied by a map from every linear associator to a thunkable one,
and vice versa.

There is another consideration, however, which injects some nuance and
exposes a particular virtue of our setting: strict or weak? We need not
choose in advance. By univalence, any suitable self-equivalence of ob
determines an inhabitant of ob ≡ ob, so object-level identifications
need not be proof-irrelevant or structurally trivial. We may therefore
proceed as if the duality were strict at the level of the ambient
carrier—ob itself can support the distinctions of polarity through
behavioral predicates—without thereby sacrificing the expressive
content of weak structure. Even when source and target are identified
at the level of objects, morphisms and their contextual actions may
still carry nontrivial coherence witnessing how that identification is
effected. This will be the pivot allowing us to move between Selinger's
strict self-dual presentation and Melliès' weaker formulations as the
development requires. Thus we can divide our investigation into the
following variance patterns for equivalences between polarized
presentations: `Pos ≃ Pos`, `Neg ≃ Neg`, and `Pos ≃ Neg` (and the
converse).

Finally, we are disposed to remark upon an implicit orientation of
Virtual Graph Theory which is perhaps strange from the conventional
categorical point of view. Ordinarily one first defines a category,
equips it with monoidal structure, and only thereafter introduces
braidings, dualities, twists, and the other phenomena of tortile
geometry as additional structure. We proceed in essentially the
opposite direction. We take the geometry underlying tortile structure
as fundamental, and recover ordinary categorical composition and
coherence as a degeneration of it.

Now we've laid the groundwork for the last consideration, which is that
we have a bit of a chicken and the egg problem, at least when it comes
to a definition of the twist. We don't yet have a notion of 'cut',
but however we go on to define the twist we need to set things up such
that this notion is sensible with regard to it.


```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Logic.Twist where

open import Core.Type
open import Cat.Logic.Type

```
