# Kitcat: A research kit for univalent mathematics and computability theory

This library written in the mathematical proof assistant, dependent type theory, and functional programming language [Agda](https://github.com/agda/agda), currently in an early stage of development, is directed towards the study of mathematics and theories of computation from the [univalent point of view](https://en.wikipedia.org/wiki/Univalent_foundations). Specifically, we focus on developing the methods of *graphical* theories of computation within type theory, such as:
* [Interaction Nets](https://wiki.xxiivv.com/site/interaction_nets.html)
* [String Diagrams](https://arxiv.org/abs/2305.08768)
* More generally, the sorts of mathematical structures defined in the rich theory underpinning [Braided](https://ncatlab.org/nlab/show/braided+monoidal+category) and [Symmetric Monoidal Categories](https://ncatlab.org/nlab/show/symmetric+monoidal+category)

## Related Work

To point towards more established work that serves as an influence for the work done here, there are many libraries hosting excellent contributions from the bright minds exploring this exciting field.

To name just five (of many more):

* [agda-categories](https://github.com/agda/agda-categories): An extensive category theory library for Agda intended to be a seamless complement to the [Agda Standard Library](https://github.com/agda/agda-stdlib). My choice of hom-typoids was aided by the approach of this library using setoids.
* [agda-prelude](https://github.com/UlfNorell/agda-prelude): Ulf Norell's Agda library geared towards performance. In particular, we aim to port over many of the modules and draw insight from Norell's library design, as he put a lot of careful work in structuring this development.
* [agda-unimath](https://unimath.github.io/agda-unimath/): By far the most organized and exhaustive explorations of univalent type theory and its applications in Agda, began by the excellent Egbert Rijke, who is responsible for a new book on the subject called Introduction to Homotopy Type Theory to be published by Cambridge but currently available as an [arXiv preprint](https://arxiv.org/abs/2212.11082). This library and text will serve as a reference point for our work.
* [TypeTopology](https://www.cs.bham.ac.uk/~mhe/TypeTopology/): The excellent "virtual blackboard" founded by Martin Escardo and which hosts both fresh and established formalized results in studies as varied as Domain Theory, Category and Game Theory. I am a current contributor at this repository.
* [1lab](https://1lab.dev/): an "experiment in discoverable formalisation: an extensive library of formalised mathematics, presented as an explorable reference resource" notable for formalizing all of its development in Cubical Agda

## Research Perspectives

A central aim of Kitcat is to survey and reevaluate results from the discipline of [Homotopy Type Theory](https://ncatlab.org/nlab/show/homotopy+type+theory) from two perspectives: 
 1. **Reinterpretation:** We revisit early and foundational results through the lens of latest developments, exploring reformulations of various topics in univalent type theory with constructions like Iosef Petrakis's [Univalent typoids](https://arxiv.org/abs/2205.06651). 
 2. **Historical Survey:** We trace back to the moment when homotopy theory inspired mathematicians like Vladimir Voevodsky to explore the applicability of topological methods to computation theory. We aim to explore this development in conjunction with Voevodsky's contemporaries who were investigating similar connections from the perspective of graph theory. 
 
## Goals

Our primary aim is to meaningfully relate results from the period "converging towards a *homotopical theory of computation*" ([Lafont, *Algebra and Geometry of Rewriting*](https://www.i2m.univ-amu.fr/~lafont/pub/agr.pdf)). Through this approach, we hope to:

* Develop novel perspectives and methods to establish new ways of distinguishing and characterizing properly 21st-century type theories, aiding and clarifying results in the latest research directions of this exciting field
* Formalize important research in the history of graphical computation theories, along with results from their predecessors in systems like Linear Logic
* Contribute to the ongoing evolution of mathematical foundations in computer science

We welcome contributions and discussions from researchers interested in these cutting-edge intersections of mathematics and computation. We maintain a mailing list hosted on sourcehut, at [~lane/kitcat-devel](https://lists.sr.ht/~lane/kitcat-devel). 
