---
artifact: nasu-logical-virtual-double-categories.tar.gz
sha256: 5b87e2ca784d6ef3d14b8c3e14210487c17d9ed1abf0ef28f5098f429fe07086
format: latex-source
fetch-url: https://arxiv.org/e-print/2501.17869
metadata-url: https://arxiv.org/abs/2501.17869
doi: 10.48550/arXiv.2501.17869
version: v2
fetched: 2026-08-10
sha256-inner: 0c1f37bbd789f9543b8c2b4f0b85d30c8233165a524e8a509b4e29b41e8efc42
---

# Nasu - Logical Aspects of Virtual Double Categories

A logical development of virtual double categories in two directions:
cartesian fibrational virtual double categories as semantics for
predicate logic, and Fibrational Virtual Double Type Theory (FVDblTT)
as a syntactic/internal language. The preliminaries give a modern
tight/loose presentation of virtual double categories and distinguish
unitality, positive-length composability, fibrationality, and
cartesianness.

Load declaration: primary logical and internal-language reference, and
a secondary presentation of the virtual-double-category fundamentals.
The map covers the full thesis source tree and is statement-deep where
the virtual structure, composition, and FVDblTT interface are defined.

## Citation

Hayato Nasu. *Logical Aspects of Virtual Double Categories*.
Master's thesis, Kyoto University, January 2025; revised version.
arXiv:2501.17869 [math.CT], v2, 31 January 2025 (v1: 15 January
2025). <https://arxiv.org/abs/2501.17869>. arXiv DOI:
10.48550/arXiv.2501.17869.

The source identifies itself as an updated version of the master's
thesis submitted to Kyoto University in January 2025
(`masterthesis.tex:142-151`).

## Vetting

Directed agent ingestion, 2026-08-10. **PROVISIONAL.**

The arXiv abstract page was opened for the bibliographic identity and
submission history. The canonical v2 e-print was hash-pinned and
extracted. The thesis abstract and contribution summary, the virtual
double category and restriction definitions, the complete composition
section, the FVDblTT introduction and core syntax/semantics, and the
syntax-semantics adjunction statement were read at the anchors below.

**No independent statement audit has been run. This entry therefore has
no `Statements verified:` field and supports no load-bearing citation
yet.** The digests below are an ingestion map, not a certification.

## Source note

`VDCpre/VDCcomp.tex:127-129` says the weaker, weakly-opcartesian notion
is "not so useful" because it "does lead" to associativity. This is an
evident omitted `not`: the cited Cruttwell-Shulman source explicitly
says the weak condition is insufficient for associativity and
unitality (`../cruttwell-shulman-generalized-multicategories/fcmonads.tex:2533-2545`),
and Nasu's own preceding phrase says the weaker notion is not useful.
The digest below records the corrected reading and keeps this source
note attached to it.

## Files

Canonical format: **LaTeX source** (the arXiv e-print). All vendored and
derived forms are gitignored; only this README is tracked.

- `nasu-logical-virtual-double-categories.tar.gz` - canonical arXiv
  source archive; the frontmatter `sha256` identifies this file.
- `masterthesis.tex` - 390-line root file, title/preface, contribution
  inventory, and chapter assembly map.
- `VDCpre/` - preliminaries: cartesian objects, double categories,
  fibrational virtual double categories, and virtual composition.
- `HDas/` - Chapter 2: fibrations, the bilateral `Bil` construction,
  comparison with other logical semantics, and translated properties.
- `FVDTT/newsubfiles/` - Chapter 3: FVDblTT introduction, syntax,
  semantics, constructors, examples, specifications, and adjunction.
- `stringdiagram/proof.tex`, `tangle.sty`, `preamble.sty` - diagram and
  document support; `masterthesis.bib` and `masterthesis.bbl` -
  bibliography sources.

The root file uses `\subfile`, so line anchors below name the included
file directly. Jump with `sed -n 'A,Bp' <file>`.

## Source provenance

Fetched by stable identifier from arXiv's e-print host on 2026-08-10.
The metadata page identified v2 as current. The source archive was
unpacked beside itself without editorial modification; the canonical
gzip-wrapper hash and gunzip-decompressed inner-tar hash are pinned in
the frontmatter. arXiv is a public host; no paywall. The root source
prints its revised-version date via `\today`; the arXiv version pin,
submission date, and artifact hashes, rather than a future compilation
date, identify this vendored vintage.

## Notation key

- Tight arrows are the vertical/categorical arrows; loose arrows are
  the horizontal arrows. A virtual cell has a finite loose-arrow source,
  a single loose-arrow target, and two tight boundaries.
- `FVDC` means *fibrational virtual double category*: all restrictions
  of loose arrows along pairs of tight arrows exist
  (`VDCpre/VDCdef.tex:360-432`). `CFVDC` adds the cartesian structure
  characterized at `VDCpre/VDCdef.tex:502-525`.
- `δ_I` is a nullary composite/unit; `⊙(α₁,...,αₙ)` is a
  composite of a positive-length loose path.
- FVDblTT has types, terms, protypes, and proterms, interpreted as
  objects, tight arrows, loose arrows, and globular virtual cells.

## Section map

### Root and preliminaries

- `masterthesis.tex:63-73` - abstract: VDC semantics for predicate
  logic and FVDblTT syntax.
- `masterthesis.tex:76-131` - thesis structure and contribution list;
  `masterthesis.tex:142-151` - revision note.
- `masterthesis.tex:156-182` - Chapter 1 assembly: cartesian objects,
  double categories, fibrational VDCs, and composition.
- `VDCpre/cartesian.tex:1-100` - cartesian objects in a 2-category.
- `VDCpre/doublecat.tex:1-2637` - double-category preliminaries,
  including double functors/transformations, companions/conjoints,
  equipments, cartesian double categories, and relations.
- `VDCpre/VDCdef.tex:1-126` - history and complete VDC definition;
  nullary cells (`VDCpre/VDCdef.tex:209-226`); double category as a VDC
  (`VDCpre/VDCdef.tex:228-248`); virtual functor and transformation
  (`VDCpre/VDCdef.tex:250-358`); restrictions/fibrationality
  (`VDCpre/VDCdef.tex:360-432`); equivalences
  (`VDCpre/VDCdef.tex:450-496`); cartesian FVDC characterization
  (`VDCpre/VDCdef.tex:502-525`); relation, matrix, profunctor, enriched,
  and internal examples (`VDCpre/VDCdef.tex:526-719`); restriction of
  cells (`VDCpre/VDCdef.tex:722-797`).
- `VDCpre/VDCcomp.tex:1-130` - composites by universal property and
  comparison with weak composites; composability taxonomy
  (`VDCpre/VDCcomp.tex:134-164`); biequivalence with double categories
  (`VDCpre/VDCcomp.tex:166-351`); equipment comparison and simplified
  fibrational test (`VDCpre/VDCcomp.tex:353-378`); cartesian unital and
  PL-composable criteria (`VDCpre/VDCcomp.tex:389-438`); examples
  (`VDCpre/VDCcomp.tex:440-489`).

### Categorical logic

- `masterthesis.tex:184-265` - Chapter 2 abstract and assembly map.
- `HDas/fibvirtintro.tex:1-387` - motivation, comparison targets, and
  overview of the double-categorical logical method.
- `HDas/background.tex:1-760` - fibrations, doctrines, elementary and
  existential structure, Beck-Chevalley, Frobenius, and related
  background.
- `HDas/fibvirt.tex:1-195` - bilateral VDC of a cartesian fibration;
  functoriality and cartesianness (`HDas/fibvirt.tex:196-951`);
  elementary-existential characterization
  (`HDas/fibvirt.tex:952-1120`); further consequences
  (`HDas/fibvirt.tex:1121-1861`).
- `HDas/charfib.tex:1-172` - regular fibrations and Beck-Chevalley
  pullbacks; Frobenius and recovery of fibrations from cartesian
  equipments (`HDas/charfib.tex:173-1029`).
- `HDas/comparison.tex:1-571` - comparison with regular categories and
  factorization systems, allegories/cartesian bicategories, and
  relational doctrines.
- `HDas/properties.tex:1-361` - predicate comprehension and tabulators;
  function extensionality/unit-pureness (`HDas/properties.tex:362-457`);
  unique choice and Cauchyness (`HDas/properties.tex:458-1135`).

### FVDblTT

- `masterthesis.tex:270-384` - Chapter 3 abstract and assembly map.
- `FVDTT/newsubfiles/introduction/intromain.tex:1-69` - formal category
  theory and FVDblTT desiderata; syntax/semantics overview
  (`:70-233`); syntax-semantics duality and constructors (`:235-387`);
  isomorphism reasoning and related work (`:388-458`).
- `FVDTT/newsubfiles/typetheory/syntax.tex:1-208` - grammar and core
  rules; signatures and associated signatures (`:209-287`);
  substitution/prosubstitution and their laws (`:290-377`);
  equational theory (`:378-470`).
- `FVDTT/newsubfiles/typetheory/inddefsem.tex:1-65` - structures and
  inductive semantics; split CFVDCs and substitution semantics
  (`:70-112`); split replacement lemma (`:114-153`).
- `FVDTT/newsubfiles/typetheory/proiso.tex:1-98` - protype
  isomorphisms and their semantics.
- `FVDTT/newsubfiles/constructor/units_thesis.tex:1-51` - path/unit
  protype; `constructor/others_thesis.tex:1-459` - composition, filler,
  and comprehension constructors; `constructor/predlogic_thesis.tex:1-45`
  - predicate-logic constructors; `appendix/cartesiansyn.tex:1-565` -
  their derivation rules; `constructor/examples.tex:1-275` - example
  calculations.
- `FVDTT/newsubfiles/adjunction/syntacticpres.tex:1-83` - presentations,
  specifications, validity, and the associated specification.
- `FVDTT/newsubfiles/adjunction/newproof.tex:1-130` - syntactic VDC and
  its split CFVDC structure; adjunction theorem (`:142-250`); protype
  isomorphism extension and relative coadjunction (`:251-546`).
- `FVDTT/newsubfiles/discussion/conclusion.tex:1-21` and
  `discussion/comparison.tex:1-75` - conclusion, future work, and
  comparison.

## Content digests

- **Virtual double category** (`VDCpre/VDCdef.tex:12`). A VDC consists
  of a category of objects and tight arrows, loose arrows between each
  object pair, `n`-ary virtual cells for every `n ≥ 0`, composition of
  cells by substituting strings of cells into the loose inputs of
  another cell, identity cells, and associativity/unit equations
  (`VDCpre/VDCdef.tex:12-126`). A nullary cell has an empty loose source
  and is drawn triangularly (`VDCpre/VDCdef.tex:209-226`).

- **Fibrationality as restriction** (`VDCpre/VDCdef.tex:360`). The
  restriction `α[s;t] : I' ⇸ J'` of a loose arrow `α : I ⇸ J`
  along tight arrows `s : I' -> I` and `t : J' -> J` is equipped with
  a restricting cell universal for cells whose tight boundaries factor
  through `s` and `t`. An FVDC has all such restrictions; a fibrational
  functor preserves them (`VDCpre/VDCdef.tex:421-432`).

- **Cartesian FVDC** (`VDCpre/VDCdef.tex:502`). An FVDC is cartesian
  exactly when its tight category has finite products, every loose
  hom-category has finite products in the stated multi-input universal
  sense, and restriction preserves those local finite products.

- **Composite and unit** (`VDCpre/VDCcomp.tex:8`). A composite of a
  path `ᾱ = (α₁,...,αₘ)` is a loose arrow `⊙ᾱ` with a
  composing cell through which any cell containing `ᾱ` as a
  consecutive block factors uniquely, including arbitrary loose
  strings before and after that block. A composite of the empty path at
  `I` is the unit `δ_I` (`VDCpre/VDCcomp.tex:103-104`).

- **Strong versus weak composite** (`VDCpre/VDCcomp.tex:113`). Nasu
  aligns the full universal property with Cruttwell-Shulman's
  opcartesian cells and calls the endpoint-only version weakly
  opcartesian. Read `VDCpre/VDCcomp.tex:128` with the omitted `not`
  recorded under Source note: the weaker condition does not supply
  associativity by itself, agreeing with the primary source.

- **Composability taxonomy** (`VDCpre/VDCcomp.tex:137`). *Unital* means
  all zero-length composites exist; *positive-length composable* means
  all nonempty paths have composites; *composable* means both. These
  are existence properties in a VDC, whereas a double category carries
  chosen horizontal composition as structure (`VDCpre/VDCcomp.tex:168-178`).

- **VDC/double-category comparison** (`VDCpre/VDCcomp.tex:168`). Every
  composable VDC can be presented as a double category, and the
  2-category of composable VDCs is biequivalent to the 2-category of
  double categories. It is not asserted to be a 2-equivalence because
  VDC composability does not choose composites while double-category
  composition is built in.

- **Fibrations and regular logic** (`HDas/fibvirt.tex:1003`). For a
  cartesian fibration `p`, the theorem states that `p` is elementary
  existential exactly when its bilateral VDC `Bil[p]` is cartesian,
  fibrational, and composable. The functorial restatement exhibits the
  elementary-existential 2-category as a pullback along `Bil`
  (`HDas/fibvirt.tex:1095-1114`).

- **Why virtuality matters logically** (`masterthesis.tex:202`).
  Composition of relations uses regular-logic structure; when equality
  or existential quantification is unavailable, the thesis argues that
  a VDC is the appropriate weakening of a double category
  (`masterthesis.tex:202-214`).

- **FVDblTT judgments**
  (`FVDTT/newsubfiles/introduction/intromain.tex:143`). Types, terms,
  protypes, and proterms interpret respectively as objects/categories,
  tight arrows/functors, loose arrows/profunctors, and globular virtual
  cells/generalized natural transformations. Fibrationality lets
  arbitrary tight boundaries be represented by restriction, so the
  syntax can keep proterm judgments linear (`:143-181`).

- **Predicate-logic reading**
  (`FVDTT/newsubfiles/introduction/intromain.tex:183`). In `Rel`,
  protypes are two-sided propositions/relations and proterms are proofs
  of Horn clauses. The interpretation table identifies the path
  protype with equality and the composition protype with relational
  composition by existential quantification (`:195-233`).

- **Core syntax and substitution**
  (`FVDTT/newsubfiles/typetheory/syntax.tex:1`). Procontexts are ordered
  finite strings of composable protypes, and proterms have such a
  string as source and one protype as target (`:29-48`). Ordinary
  substitution models restriction along tight arrows; prosubstitution
  models virtual-cell composition, with associativity/interchange laws
  stated by the substitution lemmas (`:290-377`).

- **Semantics**
  (`FVDTT/newsubfiles/typetheory/inddefsem.tex:16`). A structure maps a
  signature into a CFVDC. Protype application is interpreted by
  restriction, protype products by local products, a provariable by an
  identity cell, and a compound proterm by restricting its generating
  cell and composing it with the interpretations of its input proterms
  (`:16-65`).

- **Syntactic VDC and adjunction**
  (`FVDTT/newsubfiles/adjunction/newproof.tex:5`). From a specification,
  the syntactic VDC takes contexts as objects, term substitutions modulo
  derivable equality as tight arrows, protypes modulo equality as loose
  arrows, and proterms modulo equality as cells. It is a split CFVDC
  (`:54-130`). The resulting syntactic construction is left adjoint to
  the associated-specification functor, and every counit component is
  an equivalence in the 2-category of cartesian FVDCs (`:142-148`).

## What the source establishes

The thesis connects three views of the same virtual structure: loose
arrows and many-input cells as a weakening of double categories;
relations and profunctors as two-sided predicates with Horn-style
transformations; and FVDblTT protypes/proterms as an internal syntax.
It further identifies composability of the bilateral VDC of a
cartesian fibration with elementary-existential logical structure and
constructs a syntax-semantics adjunction whose counit is componentwise
an equivalence. Every mathematical claim in this entry is CONJECTURED
until machine-checked.
