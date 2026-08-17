---
artifact: cruttwell-shulman-generalized-multicategories.tar.gz
sha256: b27321b434f64c8ef7444bd5e48b74855d086aa10187ec82c8f492d23f129c80
format: latex-source
fetch-url: https://arxiv.org/e-print/0907.2460
metadata-url: https://arxiv.org/abs/0907.2460
doi: 10.48550/arXiv.0907.2460
version: v3
fetched: 2026-08-10
sha256-inner: 388db07b6217c8d327ed40d782ae10c19def6e8a9686329dc575d43509fb54f8
---

# Cruttwell and Shulman - A unified framework for generalized multicategories

The source that introduces the name *virtual double category* and uses
that structure to organize generalized multicategories. It gives the
unbiased virtual-cell definition, reconstructs horizontal units and
composition by opcartesian universal properties, characterizes pseudo
double categories by existence of all finite composites, develops
virtual equipments and restrictions, and relates representable
generalized multicategories to pseudoalgebras.

Load declaration: primary definition and construction reference for
virtual double categories. The map covers the full paper; digests are at
statement depth for virtual cells, composites, equipments, and
representability, and at section depth elsewhere.

## Citation

G. S. H. Cruttwell and Michael A. Shulman. *A unified framework for
generalized multicategories*. *Theory and Applications of Categories*
24 (2010), no. 21, pp. 580-655. arXiv:0907.2460 [math.CT], v3,
9 December 2010 (v1: 14 July 2009).
<https://arxiv.org/abs/0907.2460>. arXiv DOI:
10.48550/arXiv.0907.2460.

## Vetting

Directed agent ingestion, 2026-08-10. **PROVISIONAL.**

The arXiv abstract page was opened for the bibliographic identity,
submission history, journal reference, and subject. The canonical v3
e-print was hash-pinned, extracted, and the extracted source tree was
read at the line anchors below. The definition of virtual double
category, the entire composites-and-units section, the definition of
virtual equipment, the equipment comparison, the representability
criterion, and the appendix theorem on composites in `Mod` were checked
during ingestion.

**No independent statement audit has been run. This entry therefore has
no `Statements verified:` field and supports no load-bearing citation
yet.** The digests below are an ingestion map, not a certification.

## Files

Canonical format: **LaTeX source** (the arXiv e-print). All vendored and
derived forms are gitignored; only this README is tracked.

- `cruttwell-shulman-generalized-multicategories.tar.gz` - canonical
  arXiv source archive; the frontmatter `sha256` identifies this file.
- `fcmonads.tex` - 5,722-line main source and the file the reader greps.
  All line anchors below index this file.
- `diagxy.tex` - local diagram macros used by the main source.
- `fcmonads.bbl` - extracted bibliography.
- `tac.cls` - journal class bundled in the e-print.

Jump with `sed -n 'A,Bp' fcmonads.tex` from this directory.

## Source provenance

Fetched by stable identifier from arXiv's e-print host on 2026-08-10.
The metadata page identified v3 as the current version. The tarball was
unpacked beside itself without editorial modification; the canonical
gzip-wrapper hash and the gunzip-decompressed inner-tar hash are pinned
in the frontmatter. arXiv is a public host; no paywall.

## Notation key

- Objects and vertical arrows form the category `X`; horizontal arrows
  are written `X ⇸ Y` in this digest (slashed arrows in the source).
- A cell has a finite string `(p₁,...,pₙ)` as horizontal source,
  one horizontal target `q`, and vertical boundary arrows. Nullary
  horizontal sources are included.
- `p₁ ⊙ ... ⊙ pₙ` denotes a composite exhibited by an
  opcartesian cell; `U_X` denotes a nullary composite/unit.
- `Mod(X)` is the virtual double category of monoids and bimodules in
  `X`; `HKl(X,T)` is the horizontal Kleisli virtual double category.

## Section map

Line anchors are into `fcmonads.tex`.

- l.231-244 - Abstract: generalized multicategories as lax
  algebras/Kleisli monoids relative to monads on bicategories, unified
  by moving to double-categorical structures.
- l.249-684 - Introduction: multicategories and representability
  (l.252-266); survey of generalized examples (l.289-376); why lax
  bicategorical monads are inadequate (l.378-414); horizontal Kleisli
  arrows and the motivation for virtual double categories (l.416-474).
- l.700-1163 - Virtual double categories: motivation and examples;
  complete data-and-axioms definition (l.809-921); alternate historical
  names (l.923-929); matrices, spans, profunctors, and internal
  profunctors among the examples (l.940-1160).
- l.1164-1531 - Monads on a virtual double category: inputs represented
  by `T` (l.1167-1193), functors and monads, and examples.
- l.1532-2317 - Generalized multicategories: horizontal Kleisli virtual
  double category (l.1545 onward), `T`-monoids, functors,
  transformations, and the `Mod` construction.
- l.2318-2670 - Composites and units: opcartesian cells
  (l.2345-2382); composites and nullary units (l.2384-2393);
  coherence from universality (l.2395-2415); pseudo-double
  characterization (l.2425-2435); matrix/span/profunctor examples
  (l.2438-2525); weak opcartesianness (l.2533-2553); normal and strong
  functors (l.2555-2561); horizontal bicategory (l.2653-2667).
- l.2671-2859 - 2-categories of `T`-monoids, using units to recover
  vertical 2-cells and transformations.
- l.2860-3405 - Virtual equipments: cartesian cells and restrictions
  (l.2907-2950); preservation by `Mod` and `HKl` (l.2956-2992);
  virtual equipment (l.2997-3014); base-change objects and companions;
  equivalence with Wood-style equipments once composites exist
  (l.3309-3337).
- l.3406-3826 - Normalization of `T`-monoids and the relation between
  set-like and category-like presentations.
- l.3827-4368 - Representability: oplax and pseudo `T`-algebras
  (l.3853-3868); oplax-algebra/`T`-monoid comparison
  (l.3870-3906); representability criterion (l.3953-3965);
  monoidal categories as representable multicategories
  (l.3967-3979); biased/unbiased issue (l.3981-3994); virtual double
  categories as normal oplax double categories (l.3996-4019).
- l.4371-4640 - Appendix, composites in `Mod` and `HKl`: sufficient
  coequalizer hypotheses for `Mod(X)` to be an equipment
  (l.4380-4407), followed by horizontal Kleisli conditions.
- l.4641-5343 - Appendix, comparisons: cartesian monads
  (l.4655-4705), clubs (l.4707-4729), pseudomonads on `Prof`
  (l.4732-4775), `(T,V)`-algebras (l.4778-5043), non-cartesian monads
  (l.5048-5172), cartesian 2-monads (l.5176-5257), and monoidal
  pseudoalgebras (l.5260-5343).
- l.5347-5722 - Bibliography and end matter.

## Content digests

- **Virtual double category** (`fcmonads.tex:809`). A virtual double
  category consists of a vertical category, a class of horizontal
  arrows for each object pair, cells with vertical source and target
  and a finite horizontal multisource and single target, substitutional
  composition of cells, identity cells on horizontal arrows, and
  associativity and identity axioms. The finite source may have length
  zero (`fcmonads.tex:835`).

- **Why horizontal composition is absent** (`fcmonads.tex:416`). The
  horizontal Kleisli construction for a monad `T` has arrows `X ⇸ Y`
  represented by arrows `X ⇸ TY`. Without strong hypotheses on `T`,
  these arrows do not compose associatively, but their many-input cells
  still form a virtual double category (`fcmonads.tex:419-454`).

- **Horizontal Kleisli virtual double category**
  (`fcmonads.tex:1545`). For a monad `T` on `X`, `HKl(X,T)` keeps the
  vertical category of `X`; its horizontal arrows `X ⇸ Y` are the
  horizontal arrows `X ⇸ TY` of `X`, and its virtual cells use the
  monad unit, multiplication, and functorial structure. This is the
  stage in which `T`-monoids are defined.

- **Opcartesian cell and composite** (`fcmonads.tex:2345`). A cell from
  a string `(p₁,...,pₙ)` to `q`, with identity vertical boundary,
  is opcartesian when every larger cell in which that string occurs as
  a consecutive block factors through it uniquely. The string has a
  composite when it is the source of such a cell; `q` is then written
  `p₁ ⊙ ... ⊙ pₙ` (`fcmonads.tex:2384`). For `n = 0`, its
  target is the unit `U_X` (`fcmonads.tex:2387-2393`).

- **Coherence supplied by universality** (`fcmonads.tex:2395`).
  Composites and units are unique up to isomorphism; composites of
  opcartesian cells are opcartesian. Consequently, whenever the
  relevant composites exist, composition is associative and unital up
  to the coherent isomorphisms induced by unique factorization.

- **Pseudo double category characterization** (`fcmonads.tex:2425`). A
  virtual double category is a pseudo double category exactly when
  every finite composable string of horizontal arrows, including the
  zero-length strings, has a composite. The converse chooses
  composites and obtains coherence from their opcartesian universal
  properties (`fcmonads.tex:2430-2435`).

- **Weak opcartesianness is not enough by itself**
  (`fcmonads.tex:2533`). Restricting the factorization property to the
  case with no surrounding arrows defines weak opcartesianness. It does
  not by itself prove associativity or unitality. If every string has a
  weakly opcartesian cell and these cells are closed under composition,
  the paper says the full conclusion can be recovered
  (`fcmonads.tex:2541-2545`).

- **Profunctor composites** (`fcmonads.tex:2514`). If the enriching
  monoidal category has small colimits preserved by tensor on both
  sides, enriched profunctors compose by the coend
  `(p ⊙ q)(z,x) = ∫^y p(y,x) ⊗ q(z,y)`. Internal profunctors
  have analogous internal-coend composites when coequalizers exist and
  are preserved by pullback (`fcmonads.tex:2521-2525`).

- **Restriction and virtual equipment** (`fcmonads.tex:2907`). A
  restriction `q(g,f)` is the horizontal source of a cartesian cell
  into `q`, universal for cells whose vertical boundary factors through
  `f` and `g`. A virtual equipment is a virtual double category with all
  units and all restrictions (`fcmonads.tex:2997`). An equipment is a
  virtual equipment with all composites; this agrees with the
  Wood-style locally fully faithful pseudofunctor whose image arrows
  have right adjoints (`fcmonads.tex:3309-3328`).

- **Representability** (`fcmonads.tex:3953`). For a normal monad `T` on
  a virtual equipment, a normalized `T`-monoid `A ⇸^M TA` comes from
  a pseudo `T`-algebra exactly when `M ≅ A(a,1)` for some vertical
  algebra map `a : TA -> A` and the induced multiplication comparison
  is invertible. The paper calls the first condition weak
  representability and both conditions representability
  (`fcmonads.tex:3962-3965`).

- **Composites of bimodules** (`fcmonads.tex:4380`). If `X` is an
  equipment, its horizontal hom-categories have coequalizers, and
  horizontal composition preserves them on both sides, then `Mod(X)`
  is an equipment. The binary composite is the coequalizer of the two
  middle-monoid actions `p ⊙ B ⊙ q ⇉ p ⊙ q`.

## What the source establishes

The paper supplies a single double-categorical framework in which
generalized multicategories are `T`-monoids, even when horizontal
Kleisli arrows do not compose. For present virtual-double-category use,
its central deliverable is the separation between primitive virtual
cell composition and optional horizontal-arrow composition, with the
latter recovered by opcartesian cells. It also places restrictions,
units, composites, equipments, horizontal bicategories, and
representability in one vocabulary. Every mathematical claim in this
entry is CONJECTURED until machine-checked.
