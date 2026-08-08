---
author: Lane Biocini
date: 2026-07
contents: The Blackboard archive, every module of every frozen tree.
---

The Blackboard namespace imported entire. One section per archived
tree, each naming what its construction is, above the tree's own
imports. A checker run over this module covers every archived
module at once, which is what keeps the archive frozen green.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.index where
```

## Cats with explicit interchange

A category presented through a representable embedding `emb` of an
edge into the composite operators it induces. Interchange is a
field of the record, not a theorem about it. It says the two
splices of one representable composite into another agree. The
tree holds the category development and the monoidal layer with
its own legacy archive.

```agda
import Bb.CatsWithExplicitInterchange.Base
import Bb.CatsWithExplicitInterchange.Coherence
import Bb.CatsWithExplicitInterchange.Coherence.Gloss
import Bb.CatsWithExplicitInterchange.Displayed
import Bb.CatsWithExplicitInterchange.Displayed.Base
import Bb.CatsWithExplicitInterchange.Displayed.Coherence
import Bb.CatsWithExplicitInterchange.Functor
import Bb.CatsWithExplicitInterchange.Functor.Adjoint
import Bb.CatsWithExplicitInterchange.Functor.NatTrans
import Bb.CatsWithExplicitInterchange.Gist.AnchorPin
import Bb.CatsWithExplicitInterchange.Gist.CircleTensor
import Bb.CatsWithExplicitInterchange.Gist.CircleUnitorTwist
import Bb.CatsWithExplicitInterchange.Gist.CodepExtractAgree
import Bb.CatsWithExplicitInterchange.Gist.DoubleLoopTensor
import Bb.CatsWithExplicitInterchange.Gist.FaceProbe
import Bb.CatsWithExplicitInterchange.Gist.MiscFloor
import Bb.CatsWithExplicitInterchange.Gist.OpTwist
import Bb.CatsWithExplicitInterchange.Gist.Product
import Bb.CatsWithExplicitInterchange.Gist.ReadbackTwist
import Bb.CatsWithExplicitInterchange.Gist.RhoProbe
import Bb.CatsWithExplicitInterchange.Gist.SliceAnchor
import Bb.CatsWithExplicitInterchange.Groupoid
import Bb.CatsWithExplicitInterchange.Iso
import Bb.CatsWithExplicitInterchange.Limits.Coproduct
import Bb.CatsWithExplicitInterchange.Limits.Equalizer
import Bb.CatsWithExplicitInterchange.Limits.Product
import Bb.CatsWithExplicitInterchange.Limits.Pullback
import Bb.CatsWithExplicitInterchange.Limits.Terminal
import Bb.CatsWithExplicitInterchange.Monoidal
import Bb.CatsWithExplicitInterchange.Monoidal.Bifunctor
import Bb.CatsWithExplicitInterchange.Monoidal.Coherence
import Bb.CatsWithExplicitInterchange.Monoidal.Indiscrete
import Bb.CatsWithExplicitInterchange.Monoidal.Iso
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Bifunctor
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Braid
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Coherence
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Hexagon
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Indiscrete
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Iso
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Properties
import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Twist
import Bb.CatsWithExplicitInterchange.Monoidal.Properties
import Bb.CatsWithExplicitInterchange.Morphism
import Bb.CatsWithExplicitInterchange.Op
import Bb.CatsWithExplicitInterchange.Properties
import Bb.CatsWithExplicitInterchange.Terminal
import Bb.CatsWithExplicitInterchange.Type
import Bb.CatsWithExplicitInterchange.Type.Properties
```

## Unital magmoids

A magmoid is a type of objects, a family of hom-types, and a
covariant Yoneda embedding `yon`. Composition is derived from the
embedding: `f ⨾ g = yon g _ f`. A virtual graph extends a magmoid
with a contractible fiber that witnesses the identity morphism. The
tree develops neutral morphisms, units, isomorphisms, wild
equivalence, functors, natural transformations, and the product of
two virtual graphs, all over that one embedding.

```agda
import Bb.UnitalMagmoids.Base
import Bb.UnitalMagmoids.Coh
import Bb.UnitalMagmoids.Eqv
import Bb.UnitalMagmoids.Het
import Bb.UnitalMagmoids.Iso
import Bb.UnitalMagmoids.Magmoid
import Bb.UnitalMagmoids.Map
import Bb.UnitalMagmoids.Nat
import Bb.UnitalMagmoids.Neutral
import Bb.UnitalMagmoids.Neutral.Eq
import Bb.UnitalMagmoids.Prod
import Bb.UnitalMagmoids.Unit
```

## Naive virtual graph

A virtual graph in the chosen-edge form. Objects, edges, one
chosen edge `idn` at each object, and a ternary reflection into
judgments. `Base` holds that carrier and the vocabulary it
supports before any axiom. The `Gist` modules measure the form,
and the measurement is negative. No predicate over a freely chosen
edge pins it to the unit a tier projects.

```agda
import Bb.NaiveVirtualGraph.Base
import Bb.NaiveVirtualGraph.Gist.AbsorbObstruction
import Bb.NaiveVirtualGraph.Gist.CrossedUnit
import Bb.NaiveVirtualGraph.Gist.DeductiveSystem
import Bb.NaiveVirtualGraph.Gist.JudgmentLens
import Bb.NaiveVirtualGraph.Gist.PathGroupoid
import Bb.NaiveVirtualGraph.Gist.PerHandUnit
import Bb.NaiveVirtualGraph.Gist.ReflexiveVG
import Bb.NaiveVirtualGraph.Gist.SelfUnit
import Bb.NaiveVirtualGraph.Gist.StabilityShape
import Bb.NaiveVirtualGraph.Gist.StableFiber
import Bb.NaiveVirtualGraph.Gist.TwoSided
import Bb.NaiveVirtualGraph.Gist.UnitCanonical
```

## One twist

A virtual graph carrying `twist⁻` alone. The negative
invertibility tier mentions that twist only. So the tier is
stateable first, and its centre defines a positive twist. The
carrier loses a field that way, and `Cancel` refutes what the lost
field asserted.

```agda
import Bb.OneTwist.Base
import Bb.OneTwist.Cancel
import Bb.OneTwist.Models
```

## Virtual-graph category shape

An h-category: a graph, a ternary reflection, one chosen edge in
both argument slots, and readback. Readback aligns the reflection
with the edge. The record represents both cuts, and states
unitality as the contractibility of the type of neutral
idempotents. Interchange and stability are theorems here, not
fields.

```agda
import Bb.VgCategoryShape.Base
import Bb.VgCategoryShape.Parity
import Bb.VgCategoryShape.Type
import Bb.VgCategoryShape.Unit
```

## Weak deductive system

A virtual graph framed by two twists, with no readback. The axioms
are a stability tier, existence cuts indexed by it, and one
invertibility tier per twist. Every axiom is property, and the
framing is the only structure. The `Gist` modules are the
certified spikes on those definitions, countermodels among them.

```agda
import Bb.WeakDeductiveSystem.Base
import Bb.WeakDeductiveSystem.Display
import Bb.WeakDeductiveSystem.Gist.AssociatesCountermodel
import Bb.WeakDeductiveSystem.Gist.BalancedBase
import Bb.WeakDeductiveSystem.Gist.BalancedProfile
import Bb.WeakDeductiveSystem.Gist.FramedCut
import Bb.WeakDeductiveSystem.Gist.FramedGroup
import Bb.WeakDeductiveSystem.Gist.FramedInterchange
import Bb.WeakDeductiveSystem.Gist.NeutralUnit
import Bb.WeakDeductiveSystem.Gist.ReadbackTorsor
import Bb.WeakDeductiveSystem.Gist.ReflectFiber
import Bb.WeakDeductiveSystem.Gist.RxDict
import Bb.WeakDeductiveSystem.Gist.ThunkableSquare
import Bb.WeakDeductiveSystem.Gist.TwistFidelity
import Bb.WeakDeductiveSystem.Graph
import Bb.WeakDeductiveSystem.Type
```

## Virtual graphs

The minimal virtual-graph carrier: a graph `ob`, `hom` and the
representability axiom `reflect`, which sends every edge to a
judgment over its own endpoints. Terms, coterms, arguments,
conclusions, and judgments all derive from the graph fields. The
tree collects results over this carrier, with every further
hypothesis an explicit module parameter and `virtual-graph` the
only record.

```agda
import Bb.VirtualGraphs.Bool.Endo
import Bb.VirtualGraphs.Bool.Heap
import Bb.VirtualGraphs.Bool.Klein
import Bb.VirtualGraphs.Bool.Readers
import Bb.VirtualGraphs.Bool.Sleeve
import Bb.VirtualGraphs.Canonical
import Bb.VirtualGraphs.Circle.Mediation
import Bb.VirtualGraphs.Circle.Model
import Bb.VirtualGraphs.Circle.Natural
import Bb.VirtualGraphs.Circle.Polarity
import Bb.VirtualGraphs.Circle.Recognition
import Bb.VirtualGraphs.Circle.Shift
import Bb.VirtualGraphs.Circle.Thunkable
import Bb.VirtualGraphs.Circle.Torsor
import Bb.VirtualGraphs.Degenerate.Absorb
import Bb.VirtualGraphs.Degenerate.Cancellation
import Bb.VirtualGraphs.Degenerate.Chosen
import Bb.VirtualGraphs.Degenerate.CrossedUnit
import Bb.VirtualGraphs.Degenerate.Curried
import Bb.VirtualGraphs.Degenerate.Diagonal
import Bb.VirtualGraphs.Degenerate.Displaced
import Bb.VirtualGraphs.Degenerate.Display
import Bb.VirtualGraphs.Degenerate.Engine
import Bb.VirtualGraphs.Degenerate.Extraction
import Bb.VirtualGraphs.Degenerate.Gluing
import Bb.VirtualGraphs.Degenerate.Interchange
import Bb.VirtualGraphs.Degenerate.Lens
import Bb.VirtualGraphs.Degenerate.Neutral
import Bb.VirtualGraphs.Degenerate.Presentation
import Bb.VirtualGraphs.Degenerate.Readback
import Bb.VirtualGraphs.Degenerate.Reflexive
import Bb.VirtualGraphs.Degenerate.Shape
import Bb.VirtualGraphs.Degenerate.Stable
import Bb.VirtualGraphs.Degenerate.Tower
import Bb.VirtualGraphs.Degenerate.UnitShape
import Bb.VirtualGraphs.Embedding
import Bb.VirtualGraphs.Framing
import Bb.VirtualGraphs.Graph
import Bb.VirtualGraphs.Group.Abelian
import Bb.VirtualGraphs.Groupoid.Engine
import Bb.VirtualGraphs.Groupoid.Path
import Bb.VirtualGraphs.Mediation
import Bb.VirtualGraphs.Naturality
import Bb.VirtualGraphs.Pentagon
import Bb.VirtualGraphs.Polarity
import Bb.VirtualGraphs.Recognition
import Bb.VirtualGraphs.Tower
import Bb.VirtualGraphs.Twist
import Bb.VirtualGraphs.Type
import Bb.VirtualGraphs.Word.Carrier
import Bb.VirtualGraphs.Word.Census
import Bb.VirtualGraphs.Word.Defect
import Bb.VirtualGraphs.Word.Mediation
import Bb.VirtualGraphs.Word.Model
import Bb.VirtualGraphs.Word.Polarity
import Bb.VirtualGraphs.Word.Recognition
```
