---
artifact: petrakis-dep-arrows.tar.gz
sha256: 3cb80488fcee295aed19ff7bed478a8b8b373789f0f7ce7b57ab4f2c557f2317
format: latex-source
fetch-url: https://arxiv.org/e-print/2303.14754
metadata-url: https://arxiv.org/abs/2303.14754
doi: 10.48550/arXiv.2303.14754
version: v1
fetched: 2026-07-12
sha256-inner: 85ce309afdcf4b01509ebdb84158d9f91c101e58c140f343b5fd27392ae698d6
secondary-artifact: cat-dep-arrows.pdf
secondary-sha256: 2298bc0e6878f09146d2c1b3a015fdee6cdb0ec729b98972ea26cf0dc8557983
---

# Petrakis — Categories with dependent arrows

The source paper for the **categories-with-dependent-arrows**
formulation: an abstract categorical account of dependent functions
taken as primitive (family-arrows and dependent arrows), rather than
reduced to the Σ-construction. A potential mechanization target, so
the map below is line-anchored to the `.tex` at definition/theorem
depth.

## Citation

Iosif Petrakis. *Categories with dependent arrows*.
arXiv:2303.14754v1 [math.CT] (secondary: math.LO), 26 March 2023.
<https://arxiv.org/abs/2303.14754>. Author affiliation (per the
paper): Department of Computer Science, University of Verona
(iosif.petrakis@univr.it). Only v1 exists on arXiv (submission
history: `[v1] Sun, 26 Mar 2023 15:18:02 UTC`; no later version as
of ingestion). arXiv-issued DOI (per the abs page):
10.48550/arXiv.2303.14754. No journal or proceedings publication
was found (a CrossRef bibliographic search on the title, checked
2026-08-09, returned no match); the author's related talk on the
follow-on "codependent arrows" material (vendored beside this entry
as [petrakis-codep-slides](../petrakis-codep-slides/)) had not, as
of that talk, appeared as a post-proceedings paper either.

## Vetting

Provisional marker retired 2026-07-13 (Vetted, below). Originally ingested: Re-ingested 2026-07-12 by Claude (Opus 4.8) at Lane's
direction (R11 — the arXiv LaTeX e-print is canonical, superseding
PDF), via the ingestion protocol: the arXiv LaTeX e-print fetched
directly (`curl -L https://arxiv.org/e-print/2303.14754`), the
canonical artifact (the e-print `.tar.gz`) hashed, and the
extracted `.tex` read for the line-anchored map below. The document
hash was checked stable across two independent arXiv fetches. The
metadata (title, author, subjects, v1-only submission date 26 Mar
2023) was re-checked against `https://arxiv.org/abs/2303.14754`.
The theorem/definition numbering was reconciled against the
source's shared section counter (all numbered environments share
one per-section counter — see the map) and matches the numbers in
the prior PDF-based entry. Provisional marker retired 2026-07-13 (Vetted, below); was: Lane's confirmation pending (the format authority
governs what the marker means).

Format-conformance update 2026-07-13 (Claude, Fable 5): added the
Source URL and re-fetch and Content digests sections per the
updated format authority; the canonical hash was re-verified
against the vendored tarball and each digest anchor re-checked
against the vendored `.tex`. Status at that re-extraction: provisional (since retired — Vetted, below).

Prior ingestion: opened 2026-07-11 by Claude (Fable 5) from the
arXiv v1 PDF (title/abstract/subjects checked against the abs page;
definition/theorem inventory from `pdftotext`). That entry pinned
the PDF as canonical; R11 reclassifies the e-print `.tar.gz` as
canonical and the PDF as a secondary derived artifact (retained,
gitignored).

Statements verified: 8/10 CONFIRMED on first pass, 2 CORRECTED
applied (full), 2026-07-13, by verifier (Claude), @ 3cb80488; confirming re-pass clean 2026-07-13.

Vetted: 2026-07-13, Lane (ratified at Lane's explicit direction,
conveyed in-session; full-shelf ratification).

## Source errata

One systematic source typo, normalized faithful-to-intent in the
digests below (the normalized reading is what the digests state):
`Arxiv_Dep_CAT.tex:2486` (Thm 4.6's quantifier) writes
`λ ∈ dHom(a)` for the intended `λ ∈ fHom(a)` — fixed by the
definition body (`Σₐλ` needs `λ ∈ fHom(a)`, Def 3.1(i)) and by the
correct parallel at `l.1597`; the slip recurs at `l.2760` (§5's
opening prose) and `l.2873` (Thm 5.4's quantifier).

## Files

Canonical format: **LaTeX source** (an arXiv e-print). All vendored
and derived forms are gitignored; only this README is tracked.

- `petrakis-dep-arrows.tar.gz` — the canonical artifact (the arXiv
  e-print source). This is the file the frontmatter's canonical
  `sha256` is of. The e-print is a single gzip-compressed LaTeX
  file (arXiv's form for a one-file source), not a multi-file tar.
- `Arxiv_Dep_CAT.tex` — the extracted LaTeX source (the source's
  own internal filename), 3663 lines. **This is the file the reader
  greps**; regenerate with
  `gunzip -c petrakis-dep-arrows.tar.gz > Arxiv_Dep_CAT.tex`. Jump
  with `sed -n 'A,Bp' Arxiv_Dep_CAT.tex`.
- `cat-dep-arrows.pdf` — the arXiv v1 PDF compile (20 pp.); a
  secondary derived artifact, superseded as canonical by the
  e-print. Retained for convenience, gitignored; pinned by the
  frontmatter's `secondary-sha256`.

## Source provenance

Fetched directly from arXiv by stable identifier (re-ingested
2026-07-12 under R11 — the e-print canonical, superseding the
PDF); the frontmatter carries the e-print fetch URL, the abs
metadata URL, and the identity hashes (canonical, the extracted
inner-`.tex` fallback, and the retained secondary PDF). The
canonical hash was checked stable across two independent arXiv
fetches. Version pin v1 — the only version on arXiv as of
2026-07-13 (`[v1] Sun, 26 Mar 2023 15:18:02 UTC`), so the
unversioned e-print URL currently serves v1; should a later
version ever appear, pin explicitly by appending `v1` to the
e-print URL.

## Section map

Line anchors are into `Arxiv_Dep_CAT.tex`. Numbering note: the
source declares one shared per-section counter
(`\newtheorem{theorem}{...}[section]` at `l.169`, with
`definition`/`proposition`/`example`/… all `[theorem]` at
`l.170–177`), so every numbered environment in a section runs in a
single sequence (`2.1, 2.2, …`); numbers below were computed by
counting environments per section and match the prior entry. Two
labels are reused in the source — `\label{def: fcat}` on both
Def 2.1 and Def 2.8, `\label{def: dcat}` on both Def 4.1 and
Def 4.8 — so `\ref` to them is ambiguous; cite by the line anchors
here, not by label.

**Front matter:**
- `l.169–177` — the `\newtheorem` block (the shared-counter setup).
- `l.958` `\title`; `l.961` `\author`; `l.998–1009`
  `\begin{abstract}` … `\end{abstract}`; `l.993` `\maketitle`.

**§1 Introduction** (`l.1019`):
- `l.1060–1067` — the motivating framing: the building blocks of
  MLTT (**types, functions, type-families, dependent functions**),
  of BST (**sets, functions, families of sets, dependent
  functions**), and of CaT (**objects, arrows**) — the paper adds
  family-arrows and dependent arrows to close the analogy.
- `l.1070–1177` — the categorical-interpretation-of-dependency
  survey (Cartmell, Seely, Pitts, Palmgren, …) situating the work.

**§2 Categories with family-arrows** (`l.1178`):
- `l.1193` **Definition 2.1** (`\label{def: fcat}`) — *fam-category*
  (𝔣-category): to every object `a` a collection `fHom(a)` of
  **family-arrows** (λ, μ, …), with `C₂ := ⋃ fHom(a)`; a
  composition `∘ : fHom(a) × Hom(b,a) → fHom(b)` satisfying
  `(𝔣₁) λ∘1ₐ = λ` and `(𝔣₂) λ∘(f∘g) = (λ∘f)∘g`. Small / locally
  small / large family-structure defined at the end.
- `l.1274, 1292, 1320, 1328, 1338, 1414` — Examples 2.2–2.7
  (families of sets/types; constant families; family-arrows in the
  coslice; families on categories; families in a topos, after
  Pitts; weak family-arrows in the slice).
- `l.1535` **Definition 2.8** (label reused `def: fcat`) — the
  **category of family-arrows** `fHom(𝒞)` (= `𝒞₂`): the
  `fHom : 𝒞ᵒᵖ → Set` presheaf and its Grothendieck category of
  elements `Σ(𝒞, fHom)`, objects `(a, λ)`, arrows `f : (b,μ)→(a,λ)`
  with `μ = λ∘f`.

**§3 Categories with family-arrows and Sigma-objects** (`l.1592`):
- `l.1604` **Definition 3.1** (`\label{def: fscat}`) —
  *(𝔣, Σ)-category*: Sigma-objects `Σₐλ` with first projection
  `pr₁^{a,λ} : Σₐλ → a`, and for each `f∈Hom(b,a)` an operation
  `Σf` with `Σ_λ f : Σ_b(λ∘f) → Σₐλ` making the projection square a
  **pullback**, plus strictness `(σ₁) Σ_λ1ₐ = 1`, `(σ₂)
  Σ_λ(f∘g) = (Σ_λf)∘Σ_{λ∘f}g`. The source states in the abstract
  (`l.1003–1004`) and §1 (`l.1099–1102`): a `(𝔣, Σ)`-category with
  a terminal object is exactly a type-category of Pitts / category
  with attributes of Cartmell.
- `l.1706, 1738, 1763, 1834, 1869` — Examples 3.2–3.6 (trivial
  Sigma-object; Sigma-set and Sigma-type; Sigma-object of a
  constant family; weak Sigma-objects in the slice; commutative
  rings).
- `l.1938, 2055` — two propositions **commented out** in the source
  (`% \begin{proposition}`; not numbered, not part of the paper).
- `l.2135` **Proposition 3.7** (`\label{prp: transp1}`) — in a
  `(𝔣, Σ)`-category with terminal object 1, over global elements
  `i, j ∈ a`: `Σ₁λ(i)` is a subobject of `Σₐλ` with
  `pr₁^{1,λ(i)} = !`, recovering transport arrows witnessing
  equality of Sigma-objects over 1 for equal global elements.

**§4 Categories with dependent arrows** (`l.2309`):
- `l.2322` **Definition 4.1** (`\label{def: dcat}`) —
  *dep-category* (𝔡𝔦-category): to every `a` and `λ∈fHom(a)` a
  collection `dHom(a, λ)` of **dependent arrows** (Φ, Ψ, …),
  `C₃ := ⋃ dHom(a,λ)`; for `Φ∈dHom(a,λ)` and `f∈Hom(b,a)` an
  application `Φ(f)∈dHom(b, λ∘f)` with `(𝔡𝔦₁) Φ(1ₐ)=Φ`,
  `(𝔡𝔦₂) Φ(f∘g)=[Φ(f)](g)`. The dependent-function analogy
  (`i∈a, Φ∈dHom(a,λ) ⟹ Φ(i)∈dHom(1, λ(i))`) follows at
  `l.2360–2378`.
- `l.2379, 2391, 2424, 2435` — Examples 4.2–4.5 (trivial dependent
  arrows; dependent arrows in sets and types; **alternative**
  dependent arrows in BishSet; dependent arrows of constant
  families).
- `l.2485` **Theorem 4.6** (`\label{thm: typeisdi}`) — **every
  (𝔣, Σ)-category is a 𝔡𝔦-category canonically**: take
  `dHom(a,λ) := Di_a λ := { φ∈Hom(a, Σₐλ) | pr₁^{a,λ}∘φ = 1ₐ }`
  (the **dependent objects** / global sections).
- `l.2703` — Example 4.7 (dependent objects of constant families).
- `l.2731` **Definition 4.8** (label reused `def: dcat`) — the
  **category of dependent-arrows** `dHom(𝒞)` (= `𝒞₃`): the
  presheaf `dHom : fHom(𝒞)ᵒᵖ → Set` and its Grothendieck category
  `Σ(fHom(𝒞), dHom)`, objects `((a,λ), Φ)`.

**§5 Categories with dependent arrows and Sigma-objects** (`l.2752`):
- `l.2767` **Definition 5.1** (`\label{def: dscat}`) —
  *(𝔡𝔦, Σ)-category*: an `(𝔣, Σ)`-structure together with a
  **second-projection-dependent arrow**
  `pr₂^{a,λ} ∈ dHom(Σₐλ, λ∘pr₁^{a,λ})` satisfying
  `pr₂^{b, λ∘f} = pr₂^{a,λ}(Σ_λf)` — the Σ-object definition now
  uses the second projection as a dependent arrow, as in MLTT/BST.
- `l.2839, 2851` — Examples 5.2–5.3 (trivial projection-arrows;
  Sigma-objects of constant families).
- `l.2872` **Theorem 5.4** (`\label{thm: typeisdsi}`) — **every
  (𝔣, Σ)-category is a (𝔡𝔦, Σ)-category canonically**: the
  second-projection dependent arrow `pr₂^{a,λ}` is the arrow
  determined by the canonical pullback.
- `l.3082` — Example 5.5 (dependent objects of constant families).
- `l.3219` **Proposition 5.6** (`\label{prp: elsigma}`) — in a
  `(𝔡𝔦, Σ)`-category with terminal object 1, the elements
  `z ∈ Σₐλ` and their second-projection global elements
  `pr₂^{a,λ}(z) ∈ dHom(1, (λ∘pr₁^{a,λ})(z))`, recovering the
  element-level Σ-projections.

**§6 Concluding comments** (`l.3393`):
- The `C₁ / C₂ / C₃` three-dimensional picture (arrows /
  family-arrows / dependent arrows): dependency is expressed
  through the third dimension `C₃` **alone**, independently of
  Sigma-objects — contrasted with type-categories, where
  dependency is complicated and Σ-dependent. Stresses that
  `𝔡𝔦`-categories admit dependent arrows *not* generated from
  Sigma-objects (Examples 4.2, 4.4).
- Cofamily-arrows (`l.3465–3506`) — the dual notion sketched:
  cofamily-arrows over `a` with the covariant action and its two
  laws (cf₁/cf₂, the duals of 𝔣₁/𝔣₂), and the announcement that
  the codependent development is future work. (Addendum
  2026-07-13, anchor verified fresh by the code-citation review
  of the same date; the canonical artifact and its statement
  audit are untouched by this map line.)

**Bibliography** (`l.3528` `\begin{thebibliography}`, 41 items;
`l.3658` `\end{document}`).

## Content digests

Statement-level digests of the map's key items, in the source's
own terms and notation.

- **Def 2.1, fam-category (𝔣-category)** (`Arxiv_Dep_CAT.tex:1193`)
  — per object `a` a collection `fHom(a)` of family-arrows (union
  `C₂`), with a composition `∘ : fHom(a) × Hom(b,a) → fHom(b)`,
  (𝔣₁) `λ∘1ₐ = λ`, (𝔣₂) `λ∘(f∘g) = (λ∘f)∘g`.
- **Def 2.8, the category `fHom(𝒞)` = 𝒞₂** (`Arxiv_Dep_CAT.tex:1535`)
  — for a 𝔣-category 𝒞 with a locally small 𝔣-structure, the
  category of elements `Σ(𝒞, fHom)` of the presheaf
  `fHom : 𝒞ᵒᵖ → Set`, `[fHom(f)](λ) := λ∘f`: objects `(a,λ)`; an
  arrow `(b,μ) → (a,λ)` is an `f : b → a` with `μ = λ∘f`.
- **Def 3.1, (𝔣,Σ)-category** (`Arxiv_Dep_CAT.tex:1604`) — a
  𝔣-category with `Σₐλ ∈ C₀`, `pr₁^{a,λ} : Σₐλ → a`, and
  `Σ_λf : Σ_b(λ∘f) → Σₐλ` per `f ∈ Hom(b,a)`, with
  `pr₁^{a,λ}∘Σ_λf = f∘pr₁^{b,λ∘f}` a pullback square; (σ₁)
  `Σ_λ1ₐ = 1_{Σₐλ}`, (σ₂) `Σ_λ(f∘g) = (Σ_λf)∘Σ_{λ∘f}g`.
- **Prop 3.7, transport arrows** (`Arxiv_Dep_CAT.tex:2135`) — in a
  (𝔣,Σ)-category with terminal object 1, for global elements
  `i, j ∈ a`: (i) `Σ_λi` is monic, so `Σ₁λ(i)` is a subobject of
  `Σₐλ`, and `pr₁^{1,λ(i)} = !`; (ii) if `i = j`, the pullbacks
  induce `λᵢⱼ : Σ₁λ(i) → Σ₁λ(j)` and `λⱼᵢ`, forming an iso.
- **Def 4.1, dep-category (𝔡𝔦-category)** (`Arxiv_Dep_CAT.tex:2322`)
  — a 𝔣-category with, per `a` and `λ ∈ fHom(a)`, a collection
  `dHom(a,λ)` of dependent arrows (union `C₃`), and an application
  `Φ(f) ∈ dHom(b, λ∘f)` per `Φ ∈ dHom(a,λ)`, `f ∈ Hom(b,a)`, with
  (𝔡𝔦₁) `Φ(1ₐ) = Φ`, (𝔡𝔦₂) `Φ(f∘g) = [Φ(f)](g)`.
- **Thm 4.6, (𝔣,Σ) ⇒ 𝔡𝔦** (`Arxiv_Dep_CAT.tex:2485`) — every
  (𝔣,Σ)-category becomes a 𝔡𝔦-category with `dHom(a,λ) := Diₐλ :=
  {φ ∈ Hom(a, Σₐλ) ∣ pr₁^{a,λ}∘φ = 1ₐ}` (the dependent objects of
  λ); `φ(f)` is the unique pullback-induced arrow with
  `φ∘f = (Σ_λf)∘φ(f)` and `pr₁^{b,λ∘f}∘φ(f) = 1_b`.
- **Def 4.8, the category `dHom(𝒞)` = 𝒞₃** (`Arxiv_Dep_CAT.tex:2731`)
  — for a 𝔡𝔦-category 𝒞 with a locally small 𝔡𝔦-structure, the
  category of elements `Σ(fHom(𝒞), dHom)` of the presheaf
  `dHom : fHom(𝒞)ᵒᵖ → Set`, `[dHom(f)](Φ) := Φ(f)`: objects
  `((a,λ), Φ)`; an arrow `((b,μ),Ψ) → ((a,λ),Φ)` is an arrow
  `f : (b,μ) → (a,λ)` of `fHom(𝒞)` with `Ψ = Φ(f)`.
- **Def 5.1, (𝔡𝔦,Σ)-category** (`Arxiv_Dep_CAT.tex:2767`) — a
  𝔡𝔦-category with an (𝔣,Σ)-structure and, per `a`, `λ ∈ fHom(a)`,
  a second-projection-dependent arrow
  `pr₂^{a,λ} ∈ dHom(Σₐλ, λ∘pr₁^{a,λ})` satisfying
  `pr₂^{b,λ∘f} = pr₂^{a,λ}(Σ_λf)` for every `f ∈ Hom(b,a)`.
- **Thm 5.4, (𝔣,Σ) ⇒ (𝔡𝔦,Σ)** (`Arxiv_Dep_CAT.tex:2872`) — every
  (𝔣,Σ)-category with Thm 4.6's 𝔡𝔦-structure becomes a
  (𝔡𝔦,Σ)-category, `pr₂^{a,λ}` the unique arrow induced by the
  pullback of `pr₁^{a,λ}` along itself with both cone legs `1_{Σₐλ}`.
- **Prop 5.6, element-level Σ-projections** (`Arxiv_Dep_CAT.tex:3219`)
  — in a (𝔡𝔦,Σ)-category with terminal object 1, for `z, w ∈ Σₐλ`,
  with `u` the unique global element of `Σ₁λ(pr₁^{a,λ}(z))` such
  that `!∘u = 1₁` and `z = (Σ_λ pr₁^{a,λ}(z))∘u` (`u′` likewise
  for `w`): (i) `pr₂^{a,λ}(z) = pr₂^{1,λ(pr₁^{a,λ}(z))}(u)`;
  (ii) `z = w` iff `pr₁^{a,λ}(z) = pr₁^{a,λ}(w)` and `u′ = λᵢⱼ∘u`,
  `λᵢⱼ` the Prop 3.7 transport arrow between them; then
  `pr₂^{a,λ}(z) = pr₂^{a,λ}(w)`.

## What the source establishes

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked.

An abstract, categorical formulation of dependent functions taken as
*fundamental* and independent of the Σ-construction. The paper
introduces a stratified vocabulary mirroring MLTT (types, functions,
type-families, dependent functions) and Bishop Set Theory (sets,
functions, families of sets, dependent functions): to a category's
objects and arrows it adds **family-arrows** (`fHom(a)`, giving a
*fam-category* / 𝔣-category, Def 2.1) and then **dependent arrows**
(`dHom(a,λ)`, giving a *dep-category* / 𝔡𝔦-category, Def 4.1), each
with its own composition/application laws compatible with the arrow
structure. Layering Sigma-objects on family-arrows yields the
*(𝔣, Σ)-category* (Def 3.1), which with a terminal object **is
exactly** a type-category of Pitts / category with attributes of
Cartmell. The two central results are canonical passages up the
stratification: **every (𝔣, Σ)-category is a 𝔡𝔦-category** via its
dependent objects / global sections (Thm 4.6), and **every
(𝔣, Σ)-category is a (𝔡𝔦, Σ)-category** via the
second-projection-dependent arrow (Thm 5.4). The thesis (§6) is that
dependency lives natively in the third dimension `C₃` of dependent
arrows — including dependent arrows *not* arising from
Sigma-objects (Examples 4.2, 4.4) — rather than being reconstructed
from Σ. Everything recorded here is the source's own content, stated
in its own terms; every mathematical claim is CONJECTURED until
machine-checked.
