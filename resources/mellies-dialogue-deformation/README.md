---
artifact: mellies-dialogue-deformation.pdf
sha256: 183289be075d44060d59c61366438a0a838a2a3ff84432d4c5f238038792d965
format: pdf
fetch-url: https://www.irif.fr/~mellies/tensorial-logic/dialogue-categories-up-to-deformation.pdf
fetched: 2026-07-21
---

# Melliès — Dialogue categories up to deformation

## Citation

Paul-André Melliès. *Dialogue categories up to deformation*.
Manuscript, dated February 6, 2012. Laboratoire Preuves,
Programmes, Systèmes, CNRS — Université Paris Diderot.
Hosted at:
<https://www.irif.fr/~mellies/tensorial-logic/dialogue-categories-up-to-deformation.pdf>

Publication status: **unpublished manuscript**. A literature check
(2026-08-09) — a CrossRef bibliographic search on the title, the
author's DBLP bibliography (no entry mentions "deformation"), and
the author's own tensorial-logic index (the manuscript is listed by
title with no venue marking, its body text the only place
"deformation" appears on that page) — found no journal, proceedings,
or arXiv version. So "unpublished manuscript" is the correct
citation (honest negative: the search was performed and returned
nothing citable beyond the IRIF-hosted PDF), and no DOI exists to
record in this entry's frontmatter. It is the long, deformation-focused
companion of the published paper *Dialogue categories and
chiralities* (vendored beside this entry as
[mellies-dialogue-chiralities](../mellies-dialogue-chiralities/));
the two share the chirality definition, the 2-categorical
apparatus, and the coherence-theorem program, while this manuscript
additionally develops the deformation methodology, reflection
chiralities, and reflection categories.

## Vetting

PROVISIONAL — directed agent ingestion, 2026-07-21, at Lane's
direction (user-supplied file placed in the repository root for
vendoring; identity verified against the IRIF-hosted copy by hash
at ingestion time). The statement audit has not been run; the
entry supports no load-bearing citation until it is.

## Files

- `mellies-dialogue-deformation.pdf` — canonical artifact (the
  format is `pdf`; no source markup is available).
- `mellies-dialogue-deformation.pdftext` — greppable extraction,
  3618 lines, native text layer (no OCR). Provenance:
  `pdftotext mellies-dialogue-deformation.pdf
  mellies-dialogue-deformation.pdftext`, pdftotext 26.06.0
  (poppler-utils 26.06.0), run inside the repository's
  `nix develop` shell. Single-column layout; the table of contents
  is extracted at the file's tail (l.3563–3618). Readers grep the
  `.pdftext`; line anchors below point into it.

## Source provenance

The vendored file was supplied by Lane on 2026-07-21, placed in the
repository root as `dialoguecategoriesuptodeformation.pdf` for
vendoring (the `fetched:` date records this arrival; the file's
ultimate download date is not known). At ingestion time the
IRIF-hosted copy at the frontmatter URL was fetched independently
and its sha256 matched the vendored artifact exactly, so the
fetch-url retrieves this very compile. The author's IRIF
tensorial-logic index is a personal page without persistence
guarantees; the hash is the durable identity.

## Section map

Line anchors into `mellies-dialogue-deformation.pdftext`; jump with
`sed -n 'A,Bp' mellies-dialogue-deformation.pdftext`.

- l.1–23 — title, abstract, forewords (dialogue chirality announced
  as an adjunction between a monoidal category A of proofs and a
  monoidal category B of counter-proofs equivalent to A^op(0,1);
  coherence theorem strictifying every dialogue chirality).
- §1 Introduction:
  - l.24–171 — "Deformation of algebraic structures": strict
    monoidal categories, structure inherited by a category
    equivalent to a strict one, MacLane coherence read as the
    characterization of that inherited structure; pseudo-monoids in
    **Cat**; the purely homotopic account via the Boardman–Vogt
    W-construction in the folk model structure (l.164–171).
  - l.172–232 — "Deformation of dual structures": dialogue
    categories informally; dialogue structure is preserved by
    equivalence, so relaxing it requires a *stronger* notion of
    deformation; the involutive 2-category **Cat** with the 2-functor
    (−)^op : **Cat** → **Cat**^op(2) (l.211–232).
  - l.233–639 — the deformation recipe on the self-duality: chirality
    as the two-sided replacement, deformation performed inside
    **Cat** × **Cat**^op(2) (l.302), negations as involutive
    transports between A and B (l.520).
  - l.640–657 — the microcosm principle for dualities: which
    higher-dimensional dualities (the op(k) reversals) are needed to
    define dual structures at lower dimensions.
  - l.658–666 — related works: Kock on dualities in monoidal
    categories, Thielecke on continuations, the author's algebraic
    analysis of game semantics, Cockett–Seely polarized categories.
  - l.667–680 — plan.
- §2 The basic case: categories and chiralities (l.681):
  - l.685 — **Definition 1 (chirality)**: a pair (A, B) of
    categories with an adjoint equivalence ∗(−) ⊣ (−)∗ between A
    and B^op.
  - l.702–765 — 1-cells of Chi: triples (F•, F◦, F̃); unbiased
    two-isomorphism variant.
  - l.766–884 — 2-cells of Chi: pairs (θ•, θ◦) with the
    compatibility diagram (10).
  - l.885–897 — the 2-functors F : Chi → **Cat** (project the A
    side) and G : **Cat** → Chi (C ↦ (C, C^op), identity
    equivalence).
  - l.898 — **Theorem 1 (coherence theorem)**: F and G form a
    biequivalence of Cat and Chi. Proof shape l.901–1240: F ∘ G is
    *equal* to the identity on **Cat**; the whole deformation is
    carried on the chirality side by pseudo-natural transformations
    Φ : Id → G ∘ F and Ψ : G ∘ F → Id whose components are
    equivalences in Chi.
- §3 Dialogue categories (l.1244):
  - l.1260 — **Definition 2 (tensorial pole)**: an object ⊥ with
    representations φ_{x,y} : C(x ⊗ y, ⊥) ≅ C(y, x ⊸ ⊥) and
    ψ_{x,y} : C(x ⊗ y, ⊥) ≅ C(x, ⊥ ⟜ y), i.e. both negations at
    once.
  - l.1298 — **Definition 3 (dialogue category)**: a monoidal
    category equipped with a tensorial pole.
  - l.1302–1465 — the 2-category DiaCat: lax monoidal dialogue
    functors carrying a pole morphism ⊥_F; dialogue
    transformations.
  - l.1466–1545 — §3.3 an adjunction between negation and itself
    (the negation functors as an adjunction between C and C^op).
- §4 Reflection chiralities (l.1546):
  - l.1555 — **Definition 4 (reflection chirality)**: two monoidal
    categories (A, ⧀, true) and (B, ⧁, false), a monoidal
    equivalence ∗(−) ⊣ (−)∗ : A → B^op(0,1), a distributor
    ⟨−|−⟩ : A^op × B → Set, and a natural family
    χ_{m,a,b} : ⟨a ⧀ m | b⟩ → ⟨a | b ⧁ ∗m⟩ subject to a coherence
    diagram (15).
  - l.1658–1964 — the 2-category RefChi: 1-cells l.1662, 2-cells
    l.1774.
- §5 Dialogue chiralities (l.1965):
  - l.1970 — **Definition 5 (dialogue chirality)**: as Definition 4
    but with the distributor represented — an adjunction L ⊣ R
    between A and B replaces ⟨−|−⟩, with the χ family against it.
  - l.2057–2218 — the 2-category DiaChi.
  - l.2219 — **Lemma 1**: forgetting the adjunction L ⊣ R is a
    2-functor U : DiaChi → RefChi which is fully faithful (hom
    category isomorphisms).
- §6 The coherence theorem (l.2242):
  - l.2274–2317 — from a dialogue chirality to a dialogue category
    (the pole reconstructed).
  - l.2318–2470 — F on 1-cells and 2-cells; l.2471–2646 — G on
    2-cells.
  - l.2647–2995 — the pseudo-natural transformations Φ (l.2647) and
    Ψ (l.2841), component cells.
  - l.2996 — **Theorem 2 (coherence theorem)**: F and G form a
    biequivalence between DiaCat and DiaChi.
- §7 Reflection categories (l.3001): the one-sided notion reverse
  engineered from reflection chiralities; companions of dialogue
  categories (l.3390–3428 closes the comparison — the two notions
  of companionship coincide for dialogue chiralities).
- §8 Postliminary remarks (l.3429): a satisfactory dialogue
  category should also carry (x, y) ↦ x ⊸ ⊥ ⟜ y with a ternary
  representation C(x ⊗ y ⊗ z, ⊥) ≅ C(y, x ⊸ ⊥ ⟜ z); this holds
  when ⊥ is cyclic, when C is balanced or symmetric, or when C is
  biclosed (l.3429–3520).
- l.3521–3562 — references (Berger–Moerdijk on the Boardman–Vogt
  resolution is [2], l.3531).
- l.3563–3618 — table of contents (extraction places it last).

## Content digests

- **Definition 1 (chirality), l.685.** A chirality is a pair
  (A, B) of categories with an adjoint equivalence
  ∗(−) : B^op → A and (−)∗ : A → B^op. The deliberately naive
  strictification — every chirality is equivalent to (A, A^op) in
  **Cat** × **Cat**^op(2) — is noted and set aside as
  uninformative; the content lies in what the 1-cells and 2-cells
  of Chi must be.
- **Theorem 1 (coherence, basic case), l.898.** The projection
  F : Chi → **Cat** and the doubling G : **Cat** → Chi,
  G(C) = (C, C^op) with identity equivalence, form a biequivalence.
  F ∘ G equals the identity strictly; G ∘ F is connected to the
  identity by pseudo-natural equivalences Φ, Ψ built from the
  chirality's own η and ε. So a chirality is exactly "a category
  presented in two halves, up to deformation," and all deformation
  data lives in the comparison, none in **Cat**.
- **Definition 2 (tensorial pole), l.1260 + Definition 3
  (dialogue category), l.1298.** A tensorial pole is an object ⊥
  together with representations of both partial-application
  functors of C(− ⊗ −, ⊥): φ giving x ⊸ ⊥ and ψ giving ⊥ ⟜ y. A
  dialogue category is a monoidal category with a tensorial pole.
  Both negations are part of one pole; no compatibility between
  them is imposed at this stage.
- **Definition 4 (reflection chirality), l.1555.** The unbiased
  two-sided notion: monoidal categories (A, ⧀, true) of proofs and
  (B, ⧁, false) of refutations, a *monoidal* equivalence against
  B^op(0,1) (0- and 1-cells reversed), a pairing distributor
  ⟨−|−⟩ : A^op × B → Set, and the slot-shifting bijections
  χ_{m,a,b} : ⟨a ⧀ m | b⟩ ≅ ⟨a | b ⧁ ∗m⟩ natural in a, b, coherent
  in m — moving a tensorand across the pairing turns it into its
  negation on the other side.
- **Definition 5 (dialogue chirality), l.1970 + Lemma 1, l.2219.**
  A dialogue chirality is a reflection chirality whose distributor
  is representable: an adjunction L ⊣ R between A and B, with χ
  stated against it. Forgetting the adjunction is fully faithful
  into RefChi — representing the pairing adds no morphisms and no
  2-cells, it is a property-like layer over the reflection
  presentation.
- **Theorem 2 (coherence theorem), l.2996.** DiaCat and DiaChi are
  biequivalent, by the same F/G pattern as the basic case: project
  one hand versus double the category, with the deformation carried
  by pseudo-natural equivalences. This is the sense in which a
  dialogue chirality is a dialogue category "up to deformation,"
  and the strictification license for the two-sided presentation.
- **§8 remark, l.3429.** The binary pole is provisional: the
  satisfactory notion carries the two-sided cotensor x ⊸ ⊥ ⟜ y
  with a ternary representation, available when ⊥ is cyclic, C
  balanced or symmetric, or C biclosed — the pointer toward the
  braided/balanced refinements treated in
  [mellies-braided-dialogue](../mellies-braided-dialogue/).

## What the source establishes

A two-sided, deformation-theoretic reformulation of categories with
duality, in three rungs: (i) the basic coherence theorem — the
2-category of chiralities is biequivalent to **Cat**, with the
projection strictly retracting the doubling, so all comparison data
is deformation data; (ii) the unbiased reflection-chirality notion
(distributor pairing + slot-shifting χ) with the representable
dialogue-chirality case a fully faithful specialization; (iii) the
main coherence theorem, DiaCat ≃ DiaChi as 2-categories, licensing
the two-sided presentation of dialogue categories. Framing
throughout: structure "up to deformation" in the sense of MacLane
coherence, with a homotopic reading via the Boardman–Vogt
W-construction, and a microcosm principle for which op(k) dualities
a dual structure needs. Every mathematical claim here is
CONJECTURED until machine-checked.
