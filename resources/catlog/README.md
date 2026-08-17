---
artifact: catlog.tar.gz
sha256: cec4fec0715767c67ff644b524975cd3710a9025b050f00b3a079941e7216d46
format: source-tree
fetch-url: https://github.com/mikeshulman/catlog.git
metadata-url: https://github.com/mikeshulman/catlog
version: f0e166e5c8fc898b7e1f5b00d6ccaacb7cf390be
fetched: 2026-08-05
sha256-inner: 424e93e7bdec3741cf92a4212d0a65da95c130c1914fe2dbee96a8dec3081e66
---

# Shulman — Categorical logic from a categorical point of view

A working draft of lecture notes building categorical logic from the
ground up: each chapter fixes a class of type theories (unary,
simple, classical, first-order, higher-order, dependent) and
develops the matching categorical structure (posets and categories,
multicategories and polycategories, hyperdoctrines) side by side,
biased throughout toward reading logical connectives as universal
properties. An appendix develops a general theory of deductive
systems (terms, rules, variable binding) meant to underlie the
syntax of every chapter.

Full statement depth now covers two areas. In `classical.tex`, it
covers the polycategory and linear-logic tail (`l.541–593`) and the
prop apparatus that tail names as its term-syntax route (`l.5–242`).
It also covers the whole `dedsys.tex` appendix (`l.16–559`):
signatures, free algebras, judgments, rules, terms, and variable
binding. The maintainer directed this depth ahead of any citing
construction in this repository, so neither area is load-bearing yet.
Everything else in the book stays at outline depth, with no content
digests (house depth doctrine: digest depth tracks the source's
load). Re-map and digest a further subsection once a construction
depends on it.

## Citation

Michael Shulman. *Categorical logic from a categorical point of
view*. Working draft of expanded lecture notes, prepared as a
supplement to a course on higher categories and categorical logic
co-taught with Peter LeFanu Lumsdaine at the AARMS Summer School
2016 (organized by Dorette Pronk). GitHub repository
`mikeshulman/catlog`, commit `f0e166e5c8fc898b7e1f5b00d6ccaacb7cf390be`
(2020-01-23, the repository's `master` HEAD as of this ingestion).
<https://github.com/mikeshulman/catlog>. Unpublished working draft;
no DOI or arXiv identifier. Licensed CC BY-NC-SA 4.0 (Creative
Commons Attribution-NonCommercial-ShareAlike 4.0 International),
Copyright 2016 Michael Shulman — share and adapt permitted with
attribution, noncommercial use, and share-alike on derivatives.

## Vetting

PROVISIONAL. Ingested 2026-08-05 by Claude (Sonnet 5) at Lane's
direction. Fetched by `git clone https://github.com/mikeshulman/catlog.git`,
`git checkout f0e166e5c8fc898b7e1f5b00d6ccaacb7cf390be`, then
`git archive --format=tar.gz HEAD` to build the canonical tarball —
run twice independently in the same session from the same checkout;
both archive builds hashed identically (frontmatter `sha256`). The
commit pin was checked against the GitHub API
(`GET /repos/mikeshulman/catlog/branches/master` and
`GET /repos/mikeshulman/catlog/commits?sha=master`, both same
session) and matches the repository's actual `master` HEAD, with no
commit since 2020-01-23. The repository also carries a `gh-pages`
branch (holding only the compiled PDF, built by the in-tree
`updategh` script) — not vendored, since it carries no source beyond
what `master` already has.

Statements verified: 102/106 CONFIRMED (statement-level), 2026-08-05,
by verifier (Claude, Opus), @ cec4fec0. Full itemized audit at
`outputs/catlog-statement-audit.md`. Four items came back PARTIAL:
imprecise lead-in wording (`classical.tex:35-199`), a parenthetical
misattributed to only part of a rule (`classical.tex:201-236`), a
provenance note pointing at the wrong file (`classical.tex:562`), and
a rule rendered with a glyph reserved elsewhere in this entry
(`dedsys.tex:294-297`). The lead corrected all four directly against
the audit's cited source text. The corrected wording has not itself
been through a fresh independent audit pass.

## Files

Canonical format: **repository source tree** (`source-tree`; a
`git archive` of the pinned commit, predominantly LaTeX). All vendored
and derived forms are gitignored; only this README is tracked.

- `catlog.tar.gz` — the canonical artifact: a `git archive` of the
  full repository tree at the pinned commit (`.tex`, `.sty`, the one
  `.agda` file, `LICENSE.md`, the repo's own `README.md`, and the
  `updategh` build helper). This is the file the frontmatter's
  `sha256` is of.
- The `.tex`, `.sty`, and `.agda` files are also unpacked individually
  alongside the tarball, for direct grepping — byte-identical to
  their copies inside `catlog.tar.gz`.
- The repository's own `README.md` and `LICENSE.md` are **not**
  vendored as loose files (a loose copy of the source's `README.md`
  would collide with this entry's own `README.md`); both are inside
  `catlog.tar.gz`, and their content is quoted below.

  Source `README.md` (3 lines, quoted in full): "Working draft of
  expanded lecture notes. Comments and feedback are welcome. The
  file you want to compile is `catlog.tex`."

- `catlog.tex` — the compiled document's driver (905 bytes): loads
  `decls.tex` and `macros.tex`, then `\include`s the chapters below
  in reading order, plus a bibliography (`\bibliography{all}` — no
  `.bib` file ships in this repository).
- `decls.tex` (708 lines) / `macros.tex` (205 lines) — preamble:
  package loading, build-mode detection (TAC style, beamer), and the
  notational macros used throughout.
- `mathpartir.sty` — a vendored copy of Didier Rémy's `mathpartir`
  package (inference-rule typesetting), used by every chapter with
  deduction rules.
- `molecular.agda` (382 lines) — a standalone Agda formalisation
  sketch, not `\input` by any `.tex` file. Defines a base graph
  (`G₀`, `G`), a type former `ty` (`base`, `O`, `_+_`), and three
  mutually defined term judgments — `_↓_` (atomic), `_↕_` (molecular),
  `_↑_` (canonical) — matching `canonical.tex`'s own vocabulary
  ("Computation and Canonicity"; that chapter's `l.391` carries a
  `[TODO: Molecular?]` marker, so the Agda sketch anticipates content
  the prose chapter has not yet written).

## Source provenance

Fetched by `git clone` (not a pre-built tarball download): GitHub's
codeload archive endpoint does not guarantee byte-stable tarball
encoding for a fixed commit across time, so the canonical artifact
here is built locally and deterministically with `git archive`
against a pinned commit, exactly as an arXiv version pin fixes a
snapshot for a paper entry (the same commit-pin analogy the
`kraus-infty-cwf` entry adopted for its companion Agda source). The
pin is `f0e166e5c8fc898b7e1f5b00d6ccaacb7cf390be`, the `master`
branch's HEAD, confirmed via the GitHub REST API (see Vetting) —
not a tag or release (the repository has none).

The repository is a public, non-fork GitHub project (80 stargazers,
10 forks as of this ingestion), actively watched but not actively
committed to since 2020. It carries its own `LICENSE.md` (CC
BY-NC-SA 4.0, see Citation) — the first `resources/` entry in this
tree whose source repository ships an explicit license.

## Section map

Line anchors are into the individual `.tex` files (unpacked
alongside the tarball); jump with `sed -n 'A,Bp' <file>.tex`. Outline
depth throughout, except full depth for `classical.tex`'s `l.5–242`
(the prop apparatus) and `l.541–593` (the polycategory/linear-logic
tail), and for the whole of `dedsys.tex` (`l.16–559`) — marked below.
None of it is yet load-bearing for a construction here.

Notation transcription. The source's notation comes from `macros.tex`
and from the letter-family macro generators in `decls.tex`. The
renderings below hold throughout the map and the digests that follow.

Signature `\sig` is `Σ`, axiom set `\axes` is `Λ`, arity `\ay` is `ar`,
operation application `\act m` is `[m]`, the equality-signature symbol
`\equivsym` is `≡`, and the turnstile `\types` is `⊢`. The prop tensor
`\ptens` (the source's `\bullet`, list concatenation) is `•`, and the
dual `\d` is that same bullet raised, so `A\d` reads `A^•` — one glyph
in two roles in the source as well.

`decls.tex` generates one macro family per math alphabet: a `\c` prefix
is calligraphic (`\cG` is `𝒢`, `\cJ` is `𝒥`, `\cO` is `𝒪`), a `\d`
prefix is blackboard (`\dA` is `𝔸`, `\dN` is `ℕ`, `\dT` is `𝕋` — all
control sequences distinct from the bare `\d` above), an `\f` prefix is
fraktur (`\fB` is `𝔅`), a `\b` prefix is bold (`\bMag` is `Mag`,
`\bProp` is `Prop`), and a `bar` suffix is an overline (`\gbar` is `ḡ`);
the free-object macro `\F` is `𝔉`, so `\F\bProp\cG` reads `𝔉_{Prop}𝒢`.

Named functions: `\nAut` is `Aut`, `\id` is `id`, `\case` is `match₊`
and `\acase AB` is `match_{A+B}`, and `\type` is a trailing word `type`.
Rule labels `\plusE` and `\timesI` are `+E` and `×I`; the pairing macro
`\pair` is `⟨−,−⟩`; `\preceeds` is `≺`; `\vec M` is `M⃗`. Greek macros
render as their letters — `\si` and `\sigma` both as `σ`, `\ep` (the
source's `\varepsilon`) as `ε`, and likewise `α`, `β`, `η`, `μ`, `τ`,
`φ`, `ψ`, `λ`, `Γ`, `Δ`, `Φ`. A sub- or superscript with no Unicode
form is written `_{…}` or `^{…}`. One macro is left untranscribed and
flagged where it occurs: `\parr`, used once at `classical.tex:562`.

`catlog.tex` `\include`s, in order: `preface`, `intro`, `unary`,
`simple`, `classical`, `fol`, `hol`, `dtt`, and (as an appendix)
`dedsys`. Two further chapter files exist in the repository but are
**not** `\include`d by `catlog.tex` — `canonical.tex` and
`old-prop.tex`, both left as orphaned/superseded drafts (see below).

- **`preface.tex`** (16 lines) — Preface. One chapter, no sections:
  the course context (AARMS Summer School 2016) and acknowledgements.

- **`intro.tex`** (549 lines) — Introduction.
  - `l.10` Appetizer: inverses in group objects
  - `l.277` On syntax and free objects
  - `l.421` On type theory and category theory
  - `l.524` Expectations of the reader

- **`unary.tex`** (2366 lines) — Unary type theories.
  - `l.15` Posets
  - `l.166` Categories
  - `l.778` Meet-semilattices
  - `l.1156` Categories with products
  - `l.1515` Categories with coproducts
  - `l.1737` Universal properties and modularity
  - `l.1824` Presentations and theories

- **`simple.tex`** (3100 lines) — Simple type theories.
  - `l.11` Towards multicategories
  - `l.125` Introduction to multicategories
  - `l.324` Multiposets and monoidal posets
  - `l.666` Multicategories and monoidal categories
  - `l.1138` Adding products and coproducts
  - `l.1330` Some generalized multicategories
  - `l.1550` Intuitionistic logic
  - `l.2202` Simply typed `λ`-calculus
  - `l.2496` Cartesian presentations
  - `l.2757` Symmetric monoidal categories
    (a "Programming with `λ`-calculus" section is commented
    out at `l.2751`, unwritten)

- **`classical.tex`** (593 lines) — Classical type theories.
  - `l.5` Props and symmetric monoidal categories (`\label{sec:prop-smc}`)
  - `l.541` Cyclic multicategories and cosubunary polycategories
  - `l.576` Classical logic (`\label{sec:classical}` at `l.577`)
  - `l.582` Polycategories and linear logic (`\label{sec:cllin}` at `l.583`)

**Props prerequisite apparatus** (`l.5–242`, full depth — the
machinery `l.567–570` names as the route into a polycategory term
syntax):

- **Definition** (the term **prop**, `defn:prop`, `l.14–20`) — a prop is
  (1) a set of objects and (2) a symmetric strict monoidal category
  (identity associators/unitors) whose object-monoid is free on that
  set (`item:prop2`, `l.18`). `l.22–24`: objects of the monoidal
  category are written as finite lists `(A, B, …)`, the tensor
  `•` is list concatenation, the unit is `()`. `l.26–27`: the
  original Adams–MacLane props had one object, so props in this
  sense are sometimes called "colored props", an adjective the book
  drops.
- **Definition** (the term **polygraph**, unlabeled, `l.31–33`) — a set
  of objects together with a set of arrows, each with domain and
  codomain both finite lists of objects: the generating data a prop
  is freely built from.
- `l.35–199` — motivating discussion for why props, unlike the
  calculi of earlier chapters, cannot leave derivations unquotiented:
  the interchange rule for `•` gives two
  distinct-looking derivations of `f • g` (`l.37–61`) whose
  term-level equality (`eq:prop-bad-terms`, `l.64`) is non-directional;
  rather than assume that equality, the design instead forces a
  *unique* derivation by an "apply all
  functions as soon as possible" discipline. Output types are marked
  **active** to track this (`l.141–169`), and the needed permutations
  are built directly into the rules (`l.183–198`).
- **Figure** ("Type theory for props", `fig:props`, `l.201–236`) — the
  two rules of **the type theory for props under `𝒢`** (named at
  `l.242`): the *generator rule* (`l.204–220`) applies a batch of
  generators `f, …, g` and scalar generators `h, …, k` (every
  generator needing at least one active input) to a premise judgment,
  then reshuffles
  the result by a permutation `σ` and a scalar shuffle `τ`,
  both order-constrained; the *identity rule* (`l.222–232`) is the base
  case, applying only nullary-domain generators to a variable context.
  `l.238–241`: the identity rule's residual freedom is a permutation
  preserving the order of `B₁, …, C₁`, with scalar-term permutation
  absorbed into the premises. `l.242`: "This completes our definition
  of the type theory for props under `𝒢`."

**Props, remainder** (`l.244–538`, outline depth):
- `l.246–276` **Theorem** `thm:prop-tad` — a derivable term judgment's
  activeness assignment and derivation are both unique (a "depth of a
  term" argument).
- `l.281–323` admissibility chain: **Lemma** `thm:prop-symadm`
  (exchange on the right, functorially admissible), **Lemma**
  `thm:prop-onecutadm` (postcomposing with one generator is
  admissible), **Theorem** `thm:prop-cutadm` (cut is admissible).
- `l.325–441` a fully worked cut example (`l.325–397`); pre-terms and
  substitution for untyped terms (`l.401–414`); **Lemma**
  `thm:prop-cutissub` (the cut construction computes substitution),
  **Lemma** `thm:prop-presubassoc` (substitution is associative),
  **Theorem** `thm:prop-cutassoc` (cut is associative, via
  `thm:prop-tad` plus the two substitution lemmas).
- `l.442–480` **Theorem** `thm:prop-moncat` (contexts and derivable
  term judgments, modulo scalar-permutation equality, form a symmetric
  strict monoidal category `𝔉_{Prop}𝒢`); **Theorem**
  `thm:prop-initial` (`𝔉_{Prop}𝒢` is the free prop on `𝒢`, via the
  coherence theorem for symmetric monoidal categories).
- `l.482–538` presented props (generators of `≡` added freely; the
  bimonoid-antipode example from the Introduction, Sweedler notation at
  `l.492–499`); duals (`A^*` with `η`, `ε` and two triangle-style
  axioms, `l.501–511`) and the trace construction with its one-line
  cyclicity proof (`l.513–527`).

**`l.541–593` full map** ("Cyclic multicategories and cosubunary
polycategories", `l.541–575`; "Classical logic", `l.576–580`;
"Polycategories and linear logic", `l.582–588`) — draft/sketch prose
throughout: no `\begin{defn}`, `\begin{thm}`, or `\begin{lem}`
environment appears anywhere in this range. The entries below
paraphrase the substantive claims and open questions the prose
actually states, line-anchored.

- `l.544` — two motivating examples proposed but not developed:
  multivariable adjunctions (the symmetric case) and classical logic
  (the cartesian case).
- `l.546–548` — the cyclic-duality proposal: add conullary arrows,
  then call `ε : (A, A^•) → ()` the **counit of a duality** when
  composing with it gives a bijection between arrows
  `(Γ, A) → ()` and `Γ → A^•`. Symmetry of the duality is
  the further requirement that `εσ` satisfies the same counit
  condition. Conullary arrows are glossed as
  "mutual left adjunctions and proofs of contradictions," their
  universal property as "precisely proof by contradiction."
- `l.550–551` — an authorial planning question, left open: whether to
  start the chapter with the cosubunary case as the simplest one. A
  side remark: representable
  conullary arrows plus function-types give all duals, but not
  generally symmetric ones.
- `l.553–557` — a description of `A^•`'s elim/intro: elim is `ε`,
  "applying" a term of `A^•` to a term of `A` to get a conullary term;
  intro "abstracts" a conullary term over an `A`-variable into an
  `A^•`-term, with `β`/`η` stated as the universal property (a
  parenthetical query follows, "Parigot-style `μ`-abstraction"?).
  Symmetry additionally needs abstraction over an `A^•`-variable back
  into `A`. The passage calls this "closely related to Koh-Ong",
  differing by making their explicit substitutions implicit.
- `l.559` — a worked instance: for a multivariable-adjunction left
  adjoint `f : (A, B) → C` with `x:A, y:B ⊢ f(x,y) : C`, the two right
  adjoints are given as `μ`-terms, `x:A, z:C^• ⊢ μy. z(f(x,y)) : B^•`
  and `y:B, z:C^• ⊢ μx. z(f(x,y)) : A^•`
  (domain and codomain dualized to view each as a left adjoint).
- `l.562` — a one-line, undeveloped claim: adding connectives yields
  de Morgan duality `∧`/`∨` for classical logic and
  `⊗`/`\parr` (source macro; `catlog.tex:2` loads it from the `cmll`
  package, which is not vendored, so its definition is not located in
  the vendored `.tex`) in the noncartesian
  case, "leading to linearly distributive and `∗`-autonomous
  categories, and linear logic."
- `l.564–565` — a stated defect of the cosubunary approach: abstracting
  over `A^•` produces a term of an *arbitrary* type, unlike an
  ordinary intro rule (which lives in its own type former). The text
  ties this to the weirdness of classical logic by which "proof by
  contradiction" is a special rule that applies to any goal.
- `l.567–573` — the proposed remedy, also undeveloped: generalize from
  the cosubunary case to arbitrary (symmetric) polycategories, where
  `(Γ, A) → Δ ≅ Γ → (Δ, A^•)` is automatically
  symmetric (a Yoneda argument gives unit, counit, and triangle
  identities). A term syntax for polycategories is then proposed by
  mapping into a prop and characterizing the image with a "proof net"
  condition, explicitly flagged as "a lead-in to prop type theory"
  (the apparatus mapped above, `l.5–242`). Two further undeveloped
  notes: mention the mix rules; mention negation normal form "since
  it's in the literature."
- `l.576–580` (**Classical logic**, `\label{sec:classical}` at
  `l.577`) — no compiled body: the section holds only a commented-out
  (`%`) planning note, conjecturing that cartesian polycategories'
  polycomposition includes "the mix rule" and gives a direct
  structural cut-admissibility proof.
- `l.582–588` (**Polycategories and linear logic**,
  `\label{sec:cllin}` at `l.583`) — likewise no compiled body: two
  commented-out planning notes, one pointing to linearly distributive
  and `∗`-autonomous categories (deferring to a cited reference,
  `cs:wkdistrib`, for their universal characterizations and initiality
  theorems), the other naming Hughes' "Simple free star-autonomous
  categories and full coherence" as further reading.

- **`fol.tex`** (1698 lines) — First-order logic.
  - `l.4` Predicate logic
  - `l.700` First-order hyperdoctrines
  - `l.1079` Hyperdoctrines of subobjects
  - `l.1553` Comprehension
  - `l.1681` Finite-limit theories
  - `l.1690` Indexed monoidal categories

- **`hol.tex`** (8 lines) — Higher-order logic. Stub: chapter heading
  only, no body.

- **`dtt.tex`** (8 lines) — Dependent type theory. Stub: chapter
  heading only, no body.

- **`dedsys.tex`** (559 lines) — Deductive systems (appendix — the
  general term/rule apparatus the earlier chapters' syntax is built
  from).
  - `l.16` Trees and free algebras
  - `l.94` Indexed trees
  - `l.126` Free algebras with axioms
  - `l.227` Rules and deductive systems
  - `l.283` Terms
  - `l.405` Variable binding and `α`-equivalence

**`dedsys.tex` full map** (`l.16–559`, full depth throughout; the
appendix's own framing, `l.4–13`: a formal account of "judgment",
"rule", "derivation", and "binder," meant to precede `\cref{chap:unary}`
in reading order but placed as an appendix since its formalism needs
the earlier chapters' worked examples first):

- **Trees and free algebras** (`l.16–92`, `\label{sec:trees}`):
  - `l.23–25` — **Definition** (signature, unlabeled) — a set `Σ₁`
    of **operations** with an **arity** function `ar : Σ₁ → ℕ`
    (footnote at `l.23`: arbitrary cardinal arities work throughout
    except `\cref{sec:axioms}`, which would then need choice; the book
    restricts to finite arities).
  - `l.26–27` — **Definition** (`Σ`-algebra, unlabeled) — a set `A`
    with a function `[m] : A^{ar(m)} → A` for each `m ∈ Σ₁`.
    Morphisms of `Σ`-algebras form a category (`l.27`). `l.30`:
    example,
    `Σ₁ = {e, m}` with arities `0, 2` gives pointed magmas.
  - `l.33–42` — **Definitions** (unlabeled) — tree (nodes plus a
    connected, loop-free "edge existence" relation), rooted tree and
    root, the unique root-path from any node, outgoing/incoming edges,
    parent/children, descendant, branch (a non-retracing root-path),
    well-founded (no infinite branch).
  - `l.43–47` — **Definition** (`Σ`-labeled tree, unlabeled) — a
    rooted tree with a node-labeling into `Σ₁` and, per node
    labeled `m`, a bijection from its incoming edges to
    `{1, …, ar(m)}`; `WΣ` := isomorphism classes of
    well-founded `Σ`-labeled trees (empty unless some nullary
    operation exists), carrying the tautological `Σ`-algebra
    structure (`[m]` grafts `ar(m)` trees under a fresh root).
  - `l.49–51` — remark: `WΣ` is claimed the *initial* `Σ`-algebra;
    a classical set-theoretic proof follows, flagged skippable.
    Constructively, `WΣ` and its initiality are sometimes taken as
    a primitive axiom.
  - `l.53–62` **Theorem** `thm:tree-ind` — structural induction on
    `WΣ`: a subset `P` closed under every `[m]` (given
    `P`-inputs) equals `WΣ`. Proof: an element outside `P` yields,
    by contrapositive, an infinite branch, contradicting
    well-foundedness.
  - `l.64–69` **Theorem** `thm:tree-rec` — for any `Σ`-algebra `A`
    there is a unique `Σ`-algebra morphism `WΣ → A`. Proof is a
    stub: "TODO: standard argument."
  - `l.71–74` — free-algebra construction: given a set `X`, form
    `Σ[X]` by adjoining `X` as nullary operations; a `Σ[X]`-
    algebra is a `Σ`-algebra with a map from `X`, so the initial
    `Σ[X]`-algebra is the free `Σ`-algebra on `X`, giving the
    forgetful functor (`Σ`-algebras `→` sets) a left adjoint.
  - `l.76–80` — reformulation of `thm:tree-rec`: to define
    `f : WΣ → A` it suffices to give a `Σ`-algebra structure on
    `A`, i.e. define `f([m](t₁, …, t_{ar(m)}))` recursively
    assuming `f(t₁), …, f(t_{ar(m)})` already defined.
  - `l.84–87` **Exercise** `ex:wf-rigid` — a well-founded
    `Σ`-labeled tree has no nonidentity automorphism, so passing to
    isomorphism classes for `WΣ` is harmless.
  - `l.89–91` **Exercise** `ex:natw` — find `Σ` with
    `WΣ ≅ ℕ` realizing `thm:tree-ind` as ordinary induction.

- **Indexed trees** (`l.94–125`, `\label{sec:indexed-trees}`):
  - `l.97–104` — motivation: multi-sorted structures (e.g. a group
    acting on a set, two sorts); categories with fixed object set
    `𝒪` treated as an `(𝒪 × 𝒪)`-sorted structure, each
    hom-set its own sort, each triple `A, B, C` its own composition
    operation `∘_{A,B,C}`.
  - `l.106–109` — **Definition** (multi-sorted signature, unlabeled) —
    adds a set `Σ₀` of **sorts**, and per operation `m ∈ Σ₁`
    an output sort `cₘ` and input sorts `d_{m,1}, …, d_{m,ar(m)}`,
    written `m : (d_{m,1}, …, d_{m,ar(m)}) → cₘ`. "Signature" now
    defaults to this multi-sorted notion; the earlier notion is
    re-named **one-sorted signature**. Remark: a multi-sorted
    signature is essentially a multigraph (`\cref{defn:multigraph}`,
    not in this file).
  - `l.111` — **Definition** (`Σ`-algebra, multi-sorted, unlabeled)
    — a `Σ₀`-indexed family `{Aᵢ}` with a function
    `A_{d_{m,1}} × ⋯ × A_{d_{m,ar(m)}} → A_{cₘ}` per
    `m ∈ Σ₁`. `l.112–114`: worked example, sorts `{g, s}` with
    `m : (g,g) → g`, `t : (g,s) → s` — a binary operation on `A_g`
    together with an action of `A_g` on `A_s`.
  - `l.116–118` — **Definition** (`Σ`-labeled tree, multi-sorted,
    unlabeled) — as before, plus a sort-matching condition (a node's
    `k`-th child's output sort must equal that node's `k`-th input
    sort); `WΣᵢ` := isomorphism classes with root output sort `i`;
    `{WΣᵢ}_{i∈Σ₀}` carries the tautological (claimed
    initial) `Σ`-algebra structure.
  - `l.122–124` **Exercise** `ex:multi-sorted-W` — prove
    `{WΣᵢ}` is the initial `Σ`-algebra.

- **Free algebras with axioms** (`l.126–224`, `\label{sec:axioms}`):
  - `l.129–131` — motivation: the free monoid on `X` as a quotient of
    the free pointed magma that forces associativity and unitality.
    The general recipe constructs the needed congruence as *another*
    indexed free algebra.
  - `l.134–158` — worked case, the free semigroup on `X`: given
    `𝔉_{Mag}X` (free magma on `X`), a signature `Σ^≡` with
    sorts `𝔉_{Mag}X × 𝔉_{Mag}X` and five operation families
    (`l.140–144`: reflexivity nullary, symmetry unary, transitivity
    binary, congruence-for-multiplication binary, and an
    associativity-witness nullary operation per triple); a
    `Σ^≡`-algebra is a family `R(x,y)` with matching
    elements/operations (`l.146–153`); "`R(x,y)` is nonempty" is then
    shown (`l.154–156`) to be exactly an equivalence relation that is
    a congruence for the magma operation and relates the two
    associativity bracketings. `≡` := the relation read off
    the *initial* such algebra (`l.158`).
  - `l.160–177` **Theorem** `thm:free-monoid` — `𝔉_{Mag}X / ≡`
    is the free semigroup on `X`. Proof: the quotient inherits a
    well-defined associative operation from the congruence property;
    universally, any map `ψ : X → M` into a semigroup factors, via the
    induced magma map `φ` and the algebra
    `R(x,y) :≡ (φ(x) = φ(y))` for `Σ^≡`, uniquely
    through the quotient (using initiality of `≡`'s defining
    algebra).
  - `l.179–182` — **Definition** (`(Σ, Λ)`-algebra, unlabeled) —
    given a set `Λ` of **axioms**, each a pair
    `(a,b) ∈ WΣ[V]ᵢ` for some sort `i` and finite `V`, a `(Σ, Λ)`-
    algebra is a `Σ`-algebra `A` where every axiom-induced map
    `ḡ : WΣ[V] → A` (for `g : V → A`) equates
    `ḡ(a) = ḡ(b)`.
  - `l.184–191` — example: the magma associativity axiom, given as a
    labeled-tree pair; `(Σ, Λ)`-algebras in this instance are
    exactly semigroups.
  - `l.193–207` — the general free-`(Σ, Λ)`-algebra
    construction: a signature `Σ^≡` with sorts `(i, x, y)`
    for `x, y ∈ WΣ[X]ᵢ`, carrying reflexivity/symmetry/
    transitivity operations (`l.197–199`), one congruence operation
    per operation `m` of `Σ` (`l.200–204`), and one nullary
    axiom-instance operation per axiom and substitution
    `g : V → WΣ[X]` (`l.205–206`); `≡ᵢ` := the relation
    "sort `(i, a, b)` is nonempty in the initial `Σ^≡`-
    algebra" (`l.208`).
  - `l.210–212` **Theorem** `thm:tree-quotient` — each `≡ᵢ`
    is an equivalence relation and a `Σ`-congruence, and
    `{WΣ[X]ᵢ / ≡ᵢ}` is the free `(Σ, Λ)`-algebra on
    `X`. No proof is given (`\qed` immediately). `l.214`: restated as
    a recursive-definition principle (define `fᵢ` on the quotient by
    giving a compatible `Σ`-algebra map, then checking every axiom
    instance).
  - `l.218–220` **Exercise** `ex:tree-quotient` — prove
    `thm:tree-quotient`.
  - `l.222–224` **Exercise** `ex:infop-ac` — why choice is needed to
    extend `thm:tree-quotient` to infinitary operations.

- **Rules and deductive systems** (`l.227–281`, `\label{sec:rules}`):
  - `l.230–234` — setup: a sequence of signatures
    `Σ⁽¹⁾, …, Σ⁽ⁿ⁾`, each `Σ⁽ᵏ⁾`'s sorts defined
    from the initial algebras `WΣ⁽ʲ⁾`, `j < k` (e.g.
    `Σ⁽²⁾₀ = WΣ⁽¹⁾ × WΣ⁽¹⁾`); the special case
    `Σ⁽ᵏ⁾ = (Σ⁽ʲ⁾)^≡` recovers the construction of
    `\cref{sec:axioms}`.
  - `l.236–246` — **Definition** (judgment, unlabeled) — every sort of
    every `Σ⁽ᵏ⁾` is a **judgment** `𝒥`; notation table:
    categories on object set `𝒪` write sort `(A, B)` as `A ⊢ B`
    (matching the cut-ful category type theory, `\cref{sec:category-
    cutful}`; the cut-free theory shares sorts, differs in
    operations); a one-sorted `Σ⁽¹⁾` presenting objects uses the
    sort name "`type`," with `Σ⁽²⁾₀ = WΣ⁽¹⁾ × WΣ⁽¹⁾`
    for a unary type theory; multicategorical/
    polycategorical theories (`\cref{chap:simple,chap:polycats}`)
    write `Γ ⊢ Δ` for list-valued sorts; a
    `(Σ⁽ʲ⁾)^≡` sort `(𝒥, x, y)` is written
    `x ≡ y : 𝒥`.
  - `l.248–250` — **Definition** (rule, premises, conclusion,
    unlabeled) — each operation `m : (𝒥₁, …, 𝒥ₙ) → 𝒥′` of a
    `Σ⁽ᵏ⁾` is a **rule**, drawn as an inference rule with
    **premises** `𝒥₁, …, 𝒥ₙ` and **conclusion** `𝒥′`.
  - `l.252` — **Definition** (derivation, unlabeled) — each element of
    `WΣ⁽ᵏ⁾` is a **derivation** (of its root judgment), drawn by
    stacking rules into the tree's shape.
  - `l.253–269` — worked derivation-tree pairs: monoid associativity
    as two labeled trees over the semigroup sort `𝒥`; category
    associativity as two derivation trees per axiom, drawn with the
    composition rules `∘_{A,B,D}`, `∘_{A,C,D}`, and so on.
    `l.262` indexes those axioms by `A, B, C ∈ 𝒪`, although the
    displayed trees name four objects `A, B, C, D`.
  - `l.271–274` — **Definition** (deductive system, unlabeled) — the
    whole sequence `Σ⁽¹⁾, …, Σ⁽ⁿ⁾` is a **deductive
    system**. Example: the semigroup signature for `X` plus the
    monoid axiom-signature on top is one deductive system. Remark:
    "type theory" names a subclass of deductive systems, left
    undefined except ostensively, through the book's worked examples.
  - `l.275–280` **Remark** (unlabeled) — dependent type theories break
    the clean stratification, since the type in `⊢ A type` can
    contain terms from the "higher" judgment `Γ ⊢ M : B`,
    forcing one mutual induction (an "inductive-inductive
    definition"); the general idea stays the same.

- **Terms** (`l.283–403`, `\label{sec:terms}`):
  - `l.286–288` — motivation: derivations get unwieldy written as
    literal trees, so **terms** are introduced as concise syntax
    carrying enough information to reconstruct the derivation, e.g.
    `x·(y·z)` / `(x·y)·z` for the two associativity
    derivations, with rule `m` written infix.
  - `l.292–293` — convention `M : 𝒥` for a term representing a
    derivation of `𝒥`; exception, the one-sorted object judgment is
    written "`A type`" / "`⊢ A type`" rather than
    "`A : type`".
  - `l.294–297` — worked term-annotated rule: semigroup multiplication,
    premises `M : 𝒥` and `N : 𝒥`, conclusion `M·N : 𝒥`, with `M`, `N`
    read as "metavariables" for terms.
  - `l.299–303` — "terms with variables from the context"
    (`x : A ⊢ M : B`) read as a variant notation `x.M : (A ⊢ B)`;
    equality judgments `x : A ⊢ M ≡ N : B` likewise shorthand for
    `(x.M) ≡ (x.N) : (A ⊢ B)`; flags that such terms are
    considered modulo `α`-equivalence, deferred to
    `\cref{sec:alpha}`.
  - `l.307–323` — no canonical term assignment is required, only an
    algorithmic route from term to derivation tree; distinguishes
    **parsing** (building the syntax tree) from **type-checking**
    (verifying it is a valid derivation tree). Worked example: the
    cut-ful category type theory under `𝒢` has terms that are
    elements of a one-sorted free algebra with `id_A` nullary and
    `∘_A` binary per `A ∈ 𝒢₀`, so it contains ill-typed terms
    like `g ∘_B id_A` for `g ∈ 𝒢(C,D)` that type-checking must
    reject; remark that in general each judgment gets its own set of
    "potential terms."
  - `l.327–330` — since type-checking is given both a term and its
    putative type, notation can drop redundant information: the
    cut-ful composition `h ∘_{A,C,D} (g ∘_{A,B,C} f)` can be
    written `h ∘_C (g ∘_B f)`, since the target judgment
    `A ⊢ D` pins down the missing subscripts.
  - `l.332–339` **Remark** (unlabeled) — further omissions are
    possible from typing context (e.g. `h ∘ (−)` meaning
    `h ∘_C (−)` once `h : C → D` is known); a commented-out footnote
    (`l.336–338`, not compiled) sketches bidirectional type-checking
    for a canonical/atomic calculus.
  - `l.341–348` — the "bottom-up" reading of rules used for
    type-checking and proof search: a rule with premises
    `𝒥₁, 𝒥₂` read as "if we want to deduce `𝒥`, it suffices to
    have `𝒥₁` and `𝒥₂`", matching the direction a type-checker or a
    proof-search procedure actually applies it (footnote flags
    bidirectional theories as an exception).
  - `l.354–360` **Definition** `defn:terms` (**term system**) — for a
    signature `Σ`, a **term system** is a `Σ`-algebra `𝕋`
    (elements: **terms**) satisfying: (1) `item:terms-uniq`, for a
    judgment `c` and term `t ∈ 𝕋_c` there is at most one rule `m`
    and terms `s_j ∈ 𝕋_{d_j}` with `t = [m](s₁, …, sₙ)`; (2)
    `item:term-wf`, the immediate-subterm relation `s ≺ t`
    (holding when `t = [m](…)` and `s = s_j`) is well-founded.
  - `l.362–364` — since `𝕋` is a `Σ`-algebra, the unique morphism
    `WΣ → 𝕋` (from `thm:tree-rec`) sends each derivation to its
    representing term.
  - `l.366–373` **Lemma** `thm:term-system` — for a term system
    `𝕋`, that unique morphism `WΣ → 𝕋` is injective (a
    derivation is determined by its term). Proof: structural
    induction using `item:terms-uniq` to force matching head
    operations and matching arguments.
  - `l.375–376` — remark: the converse fails, and injectivity of
    `WΣ → 𝕋` does not even imply `item:terms-uniq` back (a fact
    about "globally" well-typed terms versus a "local" condition).
  - `l.378–389` — the two `defn:terms` axioms are exactly what make
    type-checking a deterministic terminating recursive algorithm
    (sketch given); a remark on computability, and that building
    `𝕋` as an initial algebra for another signature generally hands
    over `item:term-wf` for free.
  - `l.391–398` — notational convention: "annotating rules" with terms
    is shorthand for fixing a term system `𝕋` where each rule's
    operation `[m]` is given directly (example: the cut-ful
    composition rule annotated `ψ ∘_B φ`); since `𝕋` is
    usually a free algebra for another signature whose operations
    correspond directly to the rules (though not one-to-one), this
    preliminary step is normally left implicit.

- **Variable binding and `α`-equivalence** (`l.405–559`,
  `\label{sec:alpha}`):
  - `l.408–412` — framing: rejects a bare de Bruijn treatment as "a
    bit dishonest" given the book's actual use of named variables
    throughout. The chosen approach builds `α`-equivalence from
    permutation actions and follows `\cite{gp:asib,gp:aswvb,pg:freshml}`
    (see also `\cite{crole:alpha}`). The repository ships no `.bib`
    file, so those keys resolve to no titles inside the vendored
    source.
  - `l.414–416` — setup: a fixed infinite set `𝔸` of **variables**;
    a one-sorted signature `Σ` with injective `v, b : 𝔸 → Σ₁`,
    `ar(v(x)) = 0`, `ar(b(x)) = 1`. Intent: `WΣ` will supply the raw
    term syntax for some other signature, with `Σ`'s operations
    corresponding to that signature's term notations.
  - `l.418–421` — `v(x)` is a variable occurrence; `b(x)` **binds**
    `x` in its one argument, written `x.M` for `b(x)(M)`. Worked
    example: the coproduct-elimination term
    `match_{A+B}(M, u.P, v.Q)` combines a 3-ary `Σ`-operation with
    two uses of `b`.
  - `l.423–432` — `Aut(𝔸)` := the permutation group of `𝔸`
    (action written `x^σ`); the recursively-defined action of
    `Aut(𝔸)` on `WΣ`: `σ · [v(x)] = [v(x^σ)]`,
    `σ · [b(x)](M) = [b(x^σ)](σ · M)`, and
    recurse into subtrees otherwise; claimed, not spelled out, to be
    a group action.
  - `l.434–436` — freshness: finite arities plus well-foundedness
    force only finitely many variables per tree, so since `𝔸` is
    infinite, every `M ∈ WΣ` has a **fresh** variable `z ∉ M`.
  - `l.438–448` — **Definition** (`α`-equivalence `≡` on
    `WΣ`, via a signature `Σ^≡` built as in
    `\cref{sec:axioms}`, unlabeled) — `≡` is a congruence for
    every operation of `Σ` *except* `b` (so `v` gives
    `v(x) ≡ v(x)`), plus the swap rule `eq:alpha-gen`
    (`l.442–445`): from `z ∉ M`, `z ∉ N`, `z ≠ x`, `z ≠ y`,
    and `(zx)·M ≡ (zy)·N`, conclude
    `b(x)(M) ≡ b(y)(N)` (`(zx)`, `(zy)` denote transpositions).
  - `l.450–452` — worked examples: `x.x ≡ y.y`;
    `x.(x.x) ≡ x.(y.y)` (the inner binder shadows the outer, so the
    names agree after renaming); `x.(y.x)` is equivalent to neither,
    since `(zx)·(y.x) = (y.z)` differs.
  - `l.454–456` — corollary-as-remark: `x.M ≡ y.((yx)·M)` for
    any `y` fresh for `M` (a one-line transposition identity).
  - `l.458–459` — note: unlike `\cref{sec:axioms}`, no primitive
    reflexivity/symmetry/transitivity operations are added for
    `≡`; these must instead be *proved*, "itself a sort of
    cut-admissibility."
  - `l.461–472` **Lemma** `thm:alpha-adm` — seven properties of
    `≡`: `item:alpha-eqvadm` equivariance
    (`M ≡ N ⇒ σ·M ≡ σ·N`);
    `item:alpha-bindadm` congruence for binding
    (`M ≡ N ⇒ x.M ≡ x.N`); `item:alpha-gen-inv` invertibility
    of `eq:alpha-gen` (`x.M ≡ y.N ⇒ (zx)·M ≡ (zy)·N` for some fresh
    `z`); `item:alpha-refl`
    reflexivity; `item:alpha-symm` symmetry; `item:alpha-trans`
    transitivity; `item:alpha-rename` free bound-variable renaming
    (`z ∉ M ⇒ x.M ≡ z.((zx)·M)`).
  - `l.473–505` — proof of `thm:alpha-adm`: equivariance
    (`l.474–486`) is "the tricky and important one," by induction on
    the derivation of `M ≡ N` with the fresh choice `w := z^σ`
    and `τ := (z^σ y^σ) σ (zx)`; congruence-for-binding
    is then immediate; invertibility is immediate since
    `eq:alpha-gen` is the only primitive rule producing an
    `x.M ≡ y.N`-shaped equivalence (no primitive refl/symm/
    trans/bind-congruence in the presentation); reflexivity and
    symmetry follow by straightforward induction combining the
    primitive congruences with congruence-for-binding; transitivity
    (`l.492–501`) needs a non-structural, height-based induction,
    since the equivariance step invoked mid-proof is not a subtree of
    the given derivations; renaming (`l.503–504`) is a direct
    calculation via a fresh `w` and reflexivity.
  - `l.507–509` — the quotient `WΣ/≡` is "terms modulo
    `α`-equivalence of bound variables"; since `≡` is a
    congruence for every `Σ`-operation (including, via
    `thm:alpha-adm`'s `item:alpha-bindadm`, `b`/binding), every
    operation descends to the quotient.
  - `l.510–518` — intended use: restrict to the subset of
    `WΣ/≡` with the "right number of variables bound to
    represent the context" — e.g. unary type theory's
    `x : A ⊢ M : B` reads as `x.M : (A ⊢ B)`, so `𝕋` is the subset
    with one outermost binding; a simple type theory's `Γ ⊢ B` (with
    `|Γ| = n`) needs `n` outermost bindings, motivating
    `\cref{sec:terms}`'s remark that different judgments can carry
    different potential-term sets.
  - `l.520–546` — constructing term-operations on these
    binder-restricted sets, worked via `match₊` (`\cref{sec:catcoprod}`):
    to define `𝕋³ → 𝕋` representing `+E`'s three premises
    from the raw 3-ary `Σ`-operation `match₊`, choose
    representatives of `x.M`, `u.P`, `v.Q` with `x` fresh for
    `u.P`, `v.Q` (`thm:alpha-adm`'s `item:alpha-rename`), form
    `x.match₊(M, u.P, v.Q)`, and check representative-independence via
    `item:alpha-gen-inv` plus congruence and transitivity (explicit
    calculation, `l.535–540`). The same recipe applies generally,
    illustrated again by `×I`'s pairing term, which needs a
    *shared* fresh variable for two separately-bound inputs:
    `z.⟨(zx)·M, (zy)·N⟩`.
  - `l.548–552` — closing remark: any specific construction still
    needs checking against `defn:terms`; `item:term-wf` is automatic
    (`𝕋 ⊆` an initial algebra, built from at least one
    algebra operation); `item:terms-uniq` is, informally, exactly the
    "terms are derivations"/"type-checking is possible" claims used
    throughout the main text. Since every "term" here is already an
    `α`-equivalence class, no further `α`-equivalence
    reasoning is ever needed downstream.

**Not `\include`d — orphaned drafts:**

- **`canonical.tex`** (642 lines) — "Computation and Canonicity".
  - `l.23` Categories with products
  - `l.220` Categories with coproducts
  - `l.411` Focusing

  Companion territory to `molecular.agda` (see Files); carries a
  `[TODO: Molecular?]` marker at `l.391`.

- **`old-prop.tex`** (386 lines) — an untitled draft on pre-terms and
  linearity-respecting term judgments for propositional connectives
  (no `\chapter`/`\section` markup at all — prose and one inference-
  rule figure only), superseded by material now in `simple.tex` and
  `classical.tex`.

## Content digests

Statement-level digests for the two areas mapped at full depth above:
`classical.tex`'s prop apparatus (`l.5–242`) and its polycategory/
linear-logic tail (`l.541–593`), and the whole of `dedsys.tex`
(`l.16–559`). Every claim below is CONJECTURED until machine-checked
in this repository.

### `classical.tex`

- **prop** (`defn:prop`, `l.14–20`) — a set of objects plus a
  symmetric strict monoidal category, its object-monoid free on that
  set; the morphisms of the prop are the morphisms of this monoidal
  category. Objects are written as finite lists `(A, B, …)` under
  concatenation (`•`), with unit `()`.
- **polygraph** (`l.31–33`) — a set of objects with a set of arrows,
  each arrow's domain and codomain a finite list of objects: the
  free-generation data for a prop.
- **The type theory for props under `𝒢`** (`fig:props`,
  `l.201–236`, named at `l.242`) — a two-rule sequent calculus on
  judgments `Γ ⊢^𝔅 (M⃗ | Z⃗) : Δ` (context
  `Γ`, term-list `M⃗` typed `Δ`, scalar terms `Z⃗`,
  a used-label set `𝔅`). The *generator rule* applies generators
  from `𝒢` to the **active** (`l.141–142`) types of a premise,
  requiring at least one active input per generator, then reshuffles
  the conclusion by a permutation `σ` (order-preserving on
  `E⃗` and on `F₁, …, G₁`) and a scalar shuffle `τ`; the
  *identity rule* is the nullary-generator base case. This two-rule
  presentation is, by definition (`l.242`), "the type theory for
  props under `𝒢`" — the apparatus `l.567–570` proposes reusing for
  a polycategory term syntax.
- **`thm:prop-tad`** (`l.246–248`) — a derivable term judgment
  `Γ ⊢^𝔅 (M⃗ | Z⃗) : Δ` has a unique activeness
  assignment on `Δ` and a unique derivation.
- **`thm:prop-cutadm`** (`l.316–318`) — cut is admissible for the
  type theory for props: derivations of `Γ ⊢ Δ` and
  `Δ ⊢ Φ` compose to a derivation of `Γ ⊢ Φ`.
- **`thm:prop-cutissub`** (`l.417–419`) — the cut construction
  computes substitution on pre-terms: cutting `Γ ⊢ (M⃗ | Z⃗) : A⃗`
  into `x⃗ : A⃗ ⊢ (N⃗ | W⃗) : B⃗` yields
  `Γ ⊢ (N⃗[M⃗/x⃗] | W⃗[M⃗/x⃗], Z⃗) : B⃗`.
- **`thm:prop-moncat`** / **`thm:prop-initial`** (`l.458–474`) —
  contexts and derivable term judgments, modulo scalar-permutation
  equality, form a symmetric strict monoidal category `𝔉_{Prop}𝒢`,
  and this category is the free prop generated by `𝒢`.
- **Cyclic-duality proposal** (`l.546–548`) — once conullary arrows
  are allowed (the section's cyclic-multicategory setting),
  `ε : (A, A^•) → ()` is the *counit of a duality* when composing with
  `ε` gives a bijection `(Γ, A) → () ≅ Γ → A^•`.
  Symmetry of the duality is the further requirement that `εσ`
  satisfies the same counit condition.
- **`A^•`'s elim/intro** (`l.553–557`) — elim is `ε`, applying an
  `A^•`-term to an `A`-term; intro abstracts a conullary term over an
  `A`-variable into an `A^•`-term, with `β`/`η` as the universal
  property (a parenthetical query asks whether this is
  "Parigot-style `μ`-abstraction"). The symmetric case
  additionally needs the reverse abstraction, from an `A^•`-variable
  back to an `A`-term.
- **Multivariable-adjunction worked instance** (`l.559`) — for
  `f : (A, B) → C` with `x:A, y:B ⊢ f(x,y) : C`, the two induced right
  adjoints are `x:A, z:C^• ⊢ μy. z(f(x,y)) : B^•` and
  `y:B, z:C^• ⊢ μx. z(f(x,y)) : A^•`.
- **Polycategory-via-prop proposal** (`l.567–570`) — for a symmetric
  polycategory, `(Γ, A) → Δ ≅ Γ → (Δ, A^•)` is
  automatically symmetric (a Yoneda argument gives unit, counit, and
  triangle identities). A term syntax for polycategories is proposed
  by mapping into a prop and characterizing the image by a "proof
  net" condition, using the type theory for props above as its base.
- **`sec:classical`, `sec:cllin`** (`l.576–588`) — neither section
  carries a compiled body. `sec:classical`'s content is a single
  commented-out note conjecturing that cartesian polycategories'
  polycomposition includes "the mix rule" and gives a direct
  structural cut-admissibility proof. `sec:cllin`'s content is two
  commented-out notes pointing to linearly distributive and
  `∗`-autonomous categories (citing `cs:wkdistrib` for their
  universal characterizations and initiality theorems) and to
  Hughes' "Simple free star-autonomous categories and full
  coherence."

### `dedsys.tex`

- **signature / `Σ`-algebra** (`l.23–26`) — a signature is a set
  of operations with an arity function; an algebra is a carrier set
  with one function `A^{ar(m)} → A` per operation.
- **tree / `Σ`-labeled tree / `WΣ`** (`l.33–49`) — well-founded,
  rooted, labeled trees up to isomorphism; `WΣ` carries the
  free/initial `Σ`-algebra structure by grafting.
- **`thm:tree-ind`** (`l.53–56`) — structural induction on `WΣ`: a
  subset closed under every operation (given closed inputs) is all
  of `WΣ`.
- **`thm:tree-rec`** (`l.64–68`) — `WΣ` is initial: a unique
  `Σ`-algebra morphism `WΣ → A` exists for any `Σ`-algebra
  `A` (the source's proof is a stub, "TODO: standard argument").
- **free algebra via `Σ[X]`** (`l.71–74`) — adjoining `X` as
  nullary operations realizes the free `Σ`-algebra on `X` as an
  initial algebra; the forgetful functor (`Σ`-algebras `→` sets)
  has a left adjoint.
- **multi-sorted signature / indexed `WΣᵢ`** (`l.106–118`) —
  sorts `Σ₀`, each operation typed
  `m : (d_{m,1}, …, d_{m,ar(m)}) → cₘ`; `{WΣᵢ}_{i∈Σ₀}`
  is the (claimed, `ex:multi-sorted-W`) initial algebra.
- **`(Σ, Λ)`-algebra / `thm:tree-quotient`** (`l.179–212`) —
  axioms are pairs in a free algebra; the free `(Σ, Λ)`-algebra
  on `X` is a quotient `WΣ[X]ᵢ / ≡ᵢ`, with `≡ᵢ`
  itself defined via nonemptiness in an auxiliary initial algebra
  (statement given, no proof — `\qed` with no argument).
- **judgment / rule / derivation / deductive system** (`l.236–274`)
  — a **deductive system** is a finite sequence of signatures
  `Σ⁽¹⁾, …, Σ⁽ⁿ⁾`, each built from the initial algebras
  of the earlier ones. A **judgment** is any sort of any `Σ⁽ᵏ⁾`;
  a **rule** is any operation, drawn as an inference rule with
  premises and conclusion; a **derivation** is any element of
  `WΣ⁽ᵏ⁾`, drawn as a stack of rules.
- **term system, `defn:terms`** (`l.354–360`) — a `Σ`-algebra
  `𝕋` where every term has at most one operation/argument
  decomposition (`item:terms-uniq`) and the immediate-subterm
  relation is well-founded (`item:term-wf`).
- **`thm:term-system`** (`l.366–368`) — for a term system, the
  induced map `WΣ → 𝕋` is injective: a derivation is determined
  by its term.
- **binding signature / permutation action** (`l.414–431`) — a
  one-sorted `Σ` with injective `v, b : 𝔸 → Σ₁` (a
  variable-occurrence operation and a binder operation);
  `Aut(𝔸)` acts on `WΣ` by renaming through `v`/`b` and
  recursing elsewhere.
- **`α`-equivalence** (`l.438–445`) — a congruence for every
  operation except `b`, generated in addition by the swap rule
  `eq:alpha-gen`: from `z ∉ M, N`, `z ≠ x, y`, and
  `(zx)·M ≡ (zy)·N`, conclude
  `b(x)(M) ≡ b(y)(N)`.
- **`thm:alpha-adm`** (`l.461–472`) — `≡` is equivariant,
  congruent for binding, has an invertible generation rule, and is
  reflexive, symmetric, and transitive; bound variables rename
  freely.

## What the source establishes

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked in this repository.

The book's throughline (stated in its own Introduction) is that each
successive class of type theory corresponds to a successive class of
categorical structure: unary theories to categories with products
(`unary.tex`), simple theories to multicategories and monoidal
categories (`simple.tex`), classical (linear) theories to
polycategories (`classical.tex`), and first-order theories to
hyperdoctrines (`fol.tex`) — with higher-order and dependent type
theory (`hol.tex`, `dtt.tex`) left as unwritten stubs, and an
appendix (`dedsys.tex`) developing the general deductive-system
machinery (terms, rules, variable binding) the syntax of every
chapter is built on. The two `\include`-excluded chapters
(`canonical.tex` on canonicity via focusing, and the untitled
`old-prop.tex` draft) sit outside the compiled book as drafts of
varying completeness — the author's own preface (`preface.tex`)
states the notes are "currently somewhat rough, with promised
sections or chapters missing."
