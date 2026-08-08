# Changelog — kitcat lab notebook

The chronological record of what changed in this repository: what
landed, what was verified, what failed, and what it superseded.
**Newest entry first.**

- **To resume work**, read the latest session log in
  [`notes/`](notes/) (`notes/<date>-<slug>.md`) — that is where
  current state, open questions, and next steps live.
- **To understand what happened**, read down this file.
- Standing targets and their gates: [`docs/roadmap.md`](docs/roadmap.md).

This is a lab notebook, not release notes: entries are dated,
concise, and honest about verification status (`verified` /
`unverified` / `blocked` / `inferred`).

Cite a commit hash only when a session made more than one commit and
the hash disambiguates which one did what. A single-commit session
never cites its own hash: the entry is written before that commit
exists, so citing it would force a second, hash-only commit just to
close the loop. `git log --grep=<slug>` or the entry's date recovers
it in one step when needed.

---

## 2026-08-08 — Bb.VirtualGraphs: the candidate line by telescope

**Slug:** vgds-redundancy. Follow-on to the entry below.
`Recognition` and `Mediation` each held declarations at two different
telescopes, with the file boundary running across the middle rather
than between them. `Recognition`'s `candidate` and `clause` need
`ob`, `hom`, `reflect`, and a candidate; its `at-framing` needed both
half-twist families, the embedding condition, and both cuts.

Three tiers, three modules. `Recognition` keeps the bare carrier and
now imports `Type` and `Framing` alone, having pulled `Embedding`,
`Tower`, and `Mediation` before. Every external consumer of this line
reads `candidate` or `clause`, so the group they reach for stopped
dragging the tower behind it. `Canonical` is new, taking one hand:
`invertible⁺`/`invertible⁻`, holding invertibility in a hand,
two-out-of-three, and the Kraus canonicalization. `Mediation` keeps
the both-hand telescope and takes in `at-framing`, so the
judgment-level clauses and their edge-level reading sit in one file
with the bridge between them.

61, 54, and 136 code lines. `just check-tree src/Bb/VirtualGraphs`:
56 of 56. `just check Bb.index`: green.

Correction to the entry below: it says the `Word` and `Circle` models
"read one and not the other". That holds for `Circle`, whose two
models are independent. It does not hold for `Word`, where
`Word/Census` imports `Word/Mediation` and `Word/Recognition` imports
`Word/Census`. The `Word` split is a three-stage chain, so it is not
evidence about the theory pair either way, and merging the two `Word`
models would close an import cycle rather than overrun a budget.

---

## 2026-08-08 — Bb.VirtualGraphs: the diagonal is a degeneracy

**Slug:** vgds-redundancy. A redundancy and organization survey of the
55-module tree, recorded at
`notes/2026-08-08-vgds-redundancy-analysis.md`, then executed.

The finding that drove it: `Engine` was `Framing` read at the
diagonal `rx = corx = idn` and restated term for term, with the two
composites crossed. `dict` restated `Graph.graphs`, and `lens`'s
two-sided block restated `Graph.two-sided`. Setting the two
half-twist families equal is itself a degeneracy, so the criterion for
`Degenerate` widened to cover any degenerating construction, and the
five single-family modules moved: `Engine` to `Degenerate.Chosen`,
`Lens` merged into `Degenerate.Lens`, `Stable`, `Displaced`, and
`Curried` whole. `Chosen` now takes its vocabulary from
`framing G idn idn` and states the sign crossing once.

Also: readback reduced from four names to one (`framing.readback-of`);
the swap of arguments lifted from `Engine` and `Stable` into
`Embedding`, where it reads no half-twist; `Naturality` cut from
`Tower`, which fell 319 to 221 code lines; one absorption lemma in
`Degenerate.Absorb` replacing five hand-written copies, four with
identical proof terms; `Recognition`'s two laws defined as
`Mediation`'s clauses at the framing's own candidate pair;
`Degenerate.UnitShape`'s path-groupoid section moved into
`Groupoid.Path`, the last theory-module import of a model.

Eleven theory modules, twenty-one under `Degenerate`, twenty-three
models. Every theory module is inside the 300-line budget.
`just check-tree src/Bb/VirtualGraphs`: 55 of 55. `just check
Bb.index`: green. `just lint changed`: clean.

Not done: `Recognition` and `Mediation` stayed separate. Each has
model counterparts under `Word` and `Circle` that read one and not the
other, and merging the theory pair would leave four models named for a
module that no longer exists. The tree still carries 33 `refl`-only
proofs, 9 of them in `Graph`. The rule against them at
`docs/guidelines/definitions-and-proofs.md:63` is scoped to `Core`
additions, which is why an archive tree accumulated them.

---

## 2026-08-06 — spike: the symmetric readback resists both forks

**Slug:** full-readback. An Opus subagent ran the brief at
`outputs/.plans/full-readback.md` and appended its results there.
Five modules under `src/Test/NewDs/`, prefix `SpikeFullReadback`.
The lead re-ran `gtimeout 300 just check` on all five (exit 0,
2026-08-06) and read `Pinned` and `Product` in full, `Cut`,
`Quaternion`, and `Parity` at their key claims. No postulates, no
open goals: `verified`.

- Fork A (COUNTERMODEL, finite rung, H = `θnat` + `θ-neutral` +
  diagonal cut): the junction of the family with itself is
  represented by the triple rotation at `DH` (`cut-DH`), the double
  left preimage returns it (`flank-DH`, via the involution), and
  `law-A` moves the group unit. `no-law-A` at
  `SpikeFullReadbackCut.lagda.md:139`. The brief's hand-trace held
  in full.
- Fork B (COUNTERMODEL, finite rung): all three ladder rungs
  refuted, including B3, which the brief left open. One witness
  carries the ladder at `DH`: the flip family with the flip pair as
  flanks satisfies both anchors, the preimage clause, and the
  idempotence clause, and the law inverts a rotation.
  `no-derivation-B1/B2/B3` at
  `SpikeFullReadbackPinned.lagda.md:144,155,168`. The flip
  witness has a trivial double, so `SpikeFullReadbackProduct`
  removes the degeneracy: at the cyclic-times-dihedral carrier the
  family's square is central and not the unit (`double-not-unit`)
  and the full clause set still fails the law
  (`no-derivation-B3-P` at `:151`). Q₈ stands as a second B2
  witness that the idempotence clause excludes (`no-idem-Q`).
- Satisfiability: at the rotation family the pair of two double
  rotations satisfies all four clauses and the law
  (`law-B-double`), so the clause set is consistent with the law
  and does not pin the pair.
- Parity (SHADOW, cyclic rung): `reach` closes the generator under
  reflection, left-sandwich preimage, and junction
  representatives; `reach-odd` is the invariant; `no-reach-double`
  and `no-reach-unit` follow. The triple grade is reachable by two
  routes, checking the amendment's claim that the cut denotes the
  triple half-twist.

Diagnosis, standing: singular clauses through `reflect` constrain
the flank pair only up to a self-inverse edge commuting with the
family, while the law demands an edge central against every edge —
a quantifier gap. Even the law itself pins the pair only up to the
central moduli (the unit pair satisfies it wherever a unit exists).
Within the single-family apparatus the symmetric readback is
positable but neither derivable nor pinnable.

Next step: a design decision. The routes left are quantified
clauses (the law as its own axiom, `θnat`-shaped), or the
two-family framing where the primitive readback lives. Spike-zero
disposition now covers nineteen `SpikeThetaNat*` /
`SpikeTwistNeutral*` / `SpikeFullReadback*` modules.

## 2026-08-06 — withdrawn: the Selinger comparison report

Lane judged `outputs/selinger-self-dual-virtual-graphs-comparison.md`
bad and directed its removal. The file and its `.provenance.md`
sidecar are deleted. Both were uncommitted. The comparison entry
below (same date) records a delivery that no longer exists. Do not
cite the report or its strict-self-duality dictionary. The research
intermediates under `outputs/.drafts/` remain as raw material. Answer
Selinger questions from the primary source at
`resources/selinger-self-dual/SelingerSelfDual.pdftext`.

## 2026-08-06 — spike: a preimage extracts, a half-twist sandwich law does not follow

**Slug:** twist-neutral (ladder continuation, recorded in the
brief's Results as a third addendum). Context: reading readback
against Selinger's note, the faithful decoration orientation (the
term leg carries the inverse, per (1.2) and §5 of the note) turns
the flattened readback sandwich into the naturality square of the
decorating family — Lane caught an orientation error in the first
derivation, which had put the forward map on both legs. Lane then
posed the design question: drop readback as a primitive, keep the
framing on the twist, extract denoted twist and untwist edges from
the `θ-neutral` equivalences, and ask whether the readback-shaped
law over the extracted pair follows.

Two new modules, lead-written inline, each green on the first
attempt (`gtimeout 300 just check`, exit 0): `verified`.

- `SpikeTwistNeutralExtract` (GENERAL): over any carrier,
  `θ-neutral` extracts the untwist as `Equiv.inv` of the diagonal
  left sandwich map at the twist, with counit
  `θ-left (untwist x) ≡ t x`. Under `θnat` both hands extract the
  same edge (`untwist-agree`). The candidate law `θ-readback`:
  `reflect f ((x , untwist x) , (y , t y)) ≡ f`.
- `SpikeTwistNeutralDihedral` (COUNTERMODEL, finite rung, H∅ +
  `θnat` + `θ-neutral`): the dihedral carrier — eight-element
  group over `Z4 × Z2`, multiplication sandwich, rotation family —
  satisfies `θnat` (double rotation central) and `θ-neutral`
  (sandwich maps are involutions), the counit pins the untwist to
  the inverse rotation, and conjugating the flip moves it.
  `no-θ-readback` quantifies over every level-zero carrier.

Reading: `θ-readback` is naturality of the single family where
`θnat` is naturality of its double; the witness separates them by
an element with central square that is not itself central. This
matches the note's layering: the twist is natural by definition,
the half-twist is exactly the family that is not.

Correction, same day (Lane): the spiked `θ-readback` is NOT the
proposed law. The proposal is symmetric — extract the twist as a
denoted edge too (the double half-twist as one morphism, its
inverse as the untwist) and eval `f` between the extracted pair.
The spiked law flanks `f` with the extracted preimage and the
primitive family, a half-twist-grade statement, so the dihedral
verdict scopes to that law only. The intended law is unspiked; at
the dihedral carrier it holds (double rotation central). Hand-level
notes in the brief's correction addendum, amended same day: a
parity invariant blocks extracting either even-grade flank at plain
group models — and the cut does not break it, since `composite⁺`
routes through the family junction, so the cut of `(t , t)` denotes
the triple half-twist, grade 3. At plain sandwiches the intended
law is conjugation by the full twist, so the conjecture there is
derivability, not independence — but its flanks are not reachable
by extraction, only positable.

Next step: the two-fork spike, dispatched at Lane's direction
(brief at `outputs/.plans/full-readback.md`). Fork A: extraction —
`T` from the cut of `(t , t)`, `U` its double left-preimage, test
the law that pair actually supports. Fork B: posited flanks `T`,
`U` with pinning equations through `reflect`, a clause ladder with
countermodel hunts at each rung. Then the standing twist-neutral
items (circle decision, consequence structure, spike-zero
disposition — now fourteen modules).

## 2026-08-06 — spike: neutrality of the full twist at the ternary layer

**Slug:** twist-neutral. An Opus subagent ran the brief at
`outputs/.plans/twist-neutral.md`, and the results are appended
there. The condition `θ-neutral t`: both sandwich maps of `θnat`
(`θ-left`, `θ-right`) are equivalences. This is the `is-neutral`
shape of `Bb.UnitalMagmoids.Base`, with the full twist formed by
slot occupancy. Five new modules under `src/Test/NewDs/`, prefix
`SpikeTwistNeutral`. The lead re-ran
`gtimeout 300 just check Test.NewDs.<Module>` on all five (exit 0,
2026-08-06) and read `SpikeTwistNeutral`, `SpikeTwistNeutralWord`,
and `SpikeTwistNeutralCycle` in full. No postulates, no open goals:
`verified`.

The run's register: a refutation names the hypothesis theory `H` it
separates the law from, and no verdict speaks to the modeled object.

- Stage A (GENERAL): the statement, `θ-neutral-is-prop` (the
  condition is a proposition, so it imposes no truncation), and the
  halving lemmas: under `θnat` either component carries the other,
  so one `is-equiv` gives the pair.
- Stage B (COUNTERMODEL, rung Bool, H∅): refuted at `BF` with
  `const-true`, both components. An instrument check only.
- Stage C, the headline (COUNTERMODEL, rung Nat, H-BW): all four
  maps refuted at `BW`. Up to the unit laws they are `comp τ̂ ·`,
  `comp · τ̂`, `comp δ̂ ·`, and `φW`. Two fail by an unreachable
  value (`Lτ` misses `ε̂`, `Rε` misses `τ̂`) and two by a
  descriptor collision (`Rτ` forgets offset zero, `δ̂` merges
  offsets zero and one). The components do not separate at `τ̂`, so
  the halving corollary is unavailable. Two hand-traces in the
  brief were wrong and the modules correct them: `ε̂` is `comp`'s
  unit and `τ̂` the unit translation, so `R` at `τ̂` is the shift,
  not the identity, and the fiber of `Lτ` over `τ̂` is inhabited,
  so the refutation runs through the fiber over `ε̂`.
- Stage D: the Klein carrier satisfies `θ-neutral` at every family
  (`⊕-invol` makes each sandwich map its own inverse), and
  `both-KM` pairs it with `θnat-KM`: a carrier with nontrivial
  twists satisfying `θnat × θ-neutral` (SHADOW, rung Klein
  four-group). The four-reader constants and the projection carrier
  refute `θ-neutral` while satisfying `θnat` (COUNTERMODEL, rung
  Bool, H∅): `θnat` does not derive `θ-neutral`.
- Stage E (COUNTERMODEL, rung Three, H∅): a three-cycle family on
  endofunctions of a three-element type satisfies `θ-neutral` and
  fails `θnat` at a transposition. With Stage D this closes the
  independence square over H∅: neither condition derives the other.

Addenda, same day, both recorded in the brief's Results: the
hypothesis ladder under `θnat` extends two rungs without closing.
With the cycle family in both framing slots, the Stage E carrier
satisfies `is-composable⁺` and `is-composable⁻` on the nose (each
junction composite is represented with a `refl` fiber path), and it
satisfies `reflect-is-embedding` (`Three` is discrete, so the homs
are sets and the injective reflection embeds). So neither
H∅ + composability + `θ-neutral` nor
H∅ + embedding + composability + `θ-neutral` derives `θnat`.
`no-derivation` at
`src/Test/NewDs/SpikeTwistNeutralComposable.lagda.md:47` and
`no-derivation-embedding` at
`src/Test/NewDs/SpikeTwistNeutralEmbedding.lagda.md:82`, each with
a green `gtimeout 300 just check` run (exit 0): `verified`. Also
citable from existing modules: readback alone does not derive
`θnat`, since `BW` satisfies readback and fails `θnat`. Open:
readback with `θ-neutral`, undecided by every carrier on hand (the
cycle carrier fails readback, `BW` fails `θ-neutral`).

Next step: the readback rung of the ladder, then the object-facing
question, untouched by design: the circle decision (trivial
positive, with the informative modulus on the `--cubical` island)
and the package's consequence structure (`θnat × θ-neutral` as the
natural-automorphism rendering). The spike-zero disposition of the
fourteen `SpikeThetaNat*`/`SpikeTwistNeutral*` modules is pending.

## 2026-08-06 — spike: full-twist naturality at the ternary layer

**Slug:** theta-nat. An Opus subagent ran the brief at
`outputs/.plans/theta-nat.md` and appended its results there. The
predicate `θnat`: for an endo-family `t`, one `reflect` application
per side, the twist in two of the three slots
(`reflect (t x) ((x , t x) , (y , f)) ≡ reflect (t y) ((x , f) , (y , t y))`).
Five new modules under `src/Test/NewDs/`: `SpikeThetaNat`,
`SpikeThetaNatBool`, `SpikeThetaNatWord`, `SpikeThetaNatCuts`,
`SpikeThetaNatModels`. The lead re-ran
`gtimeout 300 just check Test.NewDs.<Module>` on all five (exit 0,
2026-08-06) and re-read every statement. No postulates, no open
goals: `verified`.

- Stage A: the statement compiles at the bare carrier, no theory
  module imported. The mirrored variant is the pointwise `sym`
  (GENERAL).
- Stage B: refuted at the plain-composition Bool carrier, so the
  predicate is at risk (COUNTERMODEL, rung Bool).
- Stage C, the headline: refuted at `BW` for both twists
  (`no-θnat-τ`, `no-θnat-ε`, one denotation value each). At `τ̂` the
  predicate says every descriptor commutes with the shift, and only
  the pure translations do. The expectation that the free point
  satisfies it was wrong (COUNTERMODEL, rung Nat).
- Stage D: the expected separation witness does not exist. The law
  `τ̂ ⨾⁻ f ≡ f ⨾⁻ τ̂` holds at `BW` (`far-τ⁻`). Each side of `θnat`
  there is a derived composite up to a unit law: with `τ̂` the
  predicate is `⨾⁺`-centrality of `τ̂`, with `ε̂` it is the `⨾⁻` far
  law at `ε̂`, and both fail. So at `BW` the primitive law adds no
  strength over the derived layer. It selects the cross-hand laws,
  the ones that fail there, while the own-hand far law holds
  (SHADOW + COUNTERMODEL, rung Nat).
- Stage E: the Klein carrier satisfies `θnat` at every family (the
  twist slots gather to `t ⊕ σ t`, which commutes in an abelian
  group). The projection carrier satisfies it by `refl`, degenerate.
  The four-reader carrier refutes it at `π₁` (its own twist) and
  `π₂`, and satisfies it at the constant edges
  (SHADOW / COUNTERMODEL, rung Bool). The circle stage was out of
  scope per the brief.

Next step: decide the companion condition at `BW` and the
four-reader (both `reflect`-sandwich maps are equivalences, the
`is-neutral` shape of `Bb.UnitalMagmoids.Base` at the ternary
layer). Whether `BW` separates it from `θnat` is open in both
directions: the sandwich words may or may not act invertibly on
descriptors. The spike-zero disposition of the five modules is
pending.

## 2026-08-06 — retire the vendored Test.Spike* files

**Slug:** spike-retirement. Thirteen of the fourteen `Test/Spike*`
files vendored into `Bb.VirtualGraphs` over the 2026-08-05/06
sessions still sat in `src/Test/`, untracked. Each still imported
`Cat.Logic` or `Bb.WeakDeductiveSystem` as its concrete model.
`src/Test/CLAUDE.md`'s spike-zero policy calls for removal once
content is preserved elsewhere, so all thirteen are gone:
`SpikeCandidateGenerator`, `SpikeEdgeCoherence`, `SpikeFramedShape`,
`SpikeGluingCharacteristic`, `SpikeGradeSelector`,
`SpikeMediationWild`, `SpikeNaturalModuli`, `SpikeNaturalTier`,
`SpikeNaturalTruncation`, `SpikeNeutralReadback`, `SpikeNeutralTier`,
`SpikeSelfMediation`, `SpikeTwistMediation`. `SpikeMorphismInitial`
stays; it was never vendored. `Bb.VirtualGraphs`'s own
`CHANGELOG.md`/`HISTORY.md` already record each destination, so the
policy's "name where" duty was already met.

`gtimeout 300 just check-tree src/Test`: `verified`, 17 modules.

The deletion drops `Cat.Logic`'s import-dependents to zero anywhere
in the tree, not just `Test/`. It stays live regardless.
`docs/roadmap.md` cites it as the deductive-system program's current
carrier, not archive scaffolding, so an empty dependent count does
not make it a retirement candidate. `Bb.WeakDeductiveSystem` is a
different case: `outputs/virtual-graphs-surface-weakdeductivesystem.md`
already audited all sixteen of its modules against `Bb.VirtualGraphs`
and found every one **FULLY VENDORED** or **COVERED BY OVERLAP** with
`Cat.Logic`. Its only remaining reference is now `Bb/index.lagda.md`'s
own aggregator import. It is a genuine third retirement candidate,
alongside `Bb.OneTwist`/`Bb.VgCategoryShape`. `src/Bb/TODO.md` is
updated to record it. Execution of all three stays pending, on
Lane's separate go-ahead.

## 2026-08-06 — comparison: Bb.VirtualGraphs vs Selinger self-dual

**Slug:** selinger-self-dual-virtual-graphs. Source-comparison run
of the tree against the vetted `resources/selinger-self-dual/`
digests, three passes (lead spine read, models survey, blank-slate
independent map), verifier-checked (PASS, 6 anchor fixes, 0
unresolved). Output: `outputs/selinger-self-dual-virtual-graphs-comparison.md`
with sidecar.

Graded verdict on the implicit-description thesis. As
instantiation: refuted, `verified` at anchor level (no tensor, no
dual object, no `h_A`; fourteen of nineteen digest subjects
ABSENT). As shared questions and proof strategies: confirmed, with
one on-the-nose equation (twist naturality vs `nat±-law`) and a
ranked ANALOG cluster (Word.Census `ω̂` vs Theorem 3.6,
Presentation round-trip vs Theorem 4.1, Circle non-canonicity vs
Example 3.9). As occupying §5's open design space one level down:
plausible, recorded as labeled interpretation (`inferred`), not a
checked correspondence. The collapse theorems in
`Interchange.tortile` mark the compact-closed boundary under that
reading.

`Displaced.lagda.md` appeared untracked in the tree mid-run from a
writer outside this run and was left untouched.

Next: discussion with Lane on the report; if the thesis is to
become a theorem, the open question is a tensor-bearing extension
of the carrier (delooping or argument-level pairing) and whether
the interchange gap then yields the §1.3 forced braiding.



**Slug:** deps-tool. New `bin/deps`, `bin/deps-congruence`, and
`just` recipes for both. All query results below `verified` by
hand-checks against sources.

`extract` typechecks the scope through a transient generated
umbrella (`src/DepsUmbrella.agda`, now gitignored) and parses the
Agda HTML backend's per-token anchors into a graph of single
definitions at `_build/deps/graph.json`. Queries: `deps`, `rdeps`
(direct, `--depth`, `-t`), `why` (shortest chain), `ls`, `dump`
(tsv, json, dot, `--modules` aggregation). Names resolve by
qualified name, unique suffix, module, or path. Queries warn when
sources changed after extraction.

The graph pierces re-exports and renamings: uses of a name resolve
to its definition site, so module-grain rollups report the true
providers, not the written imports. Nested structure (fields,
constructors, where-locals) carries parent chains. Layout emulation
attributes each use site to its enclosing definition. Extraction is
deterministic (byte-identical across runs, `verified`).

The graph also records the public re-export map (schema 2): every
`open ... public` statement with its `using`, `hiding`, and
`renaming` detail, name-precise, with nested-module facades
attributed to their file. Renaming aliases no longer nest inside
each other in qualified names (`Core.Type._⊔_`, not
`Core.Type.Type._⊔_`), and renaming blocks no longer emit spurious
edges.

`bin/deps-congruence` is the progressive-disclosure report over the
cache. Neither tool holds organizational claims: `extract` has no
default exclusions, and the report's strata ranks, exemptions, and
sanctioned floors arrive as invocation flags. The
`just deps-congruence` recipe states the repository's current
claims, as the `stats` recipe already does for its filters. Check A: strata-order
violations, currently 0, `verified`. Check B: under-disclosure,
reach-down through the cheapest public access point, facade-aware.
Check C: over-disclosure, a public floor shallower than every
consumer's common subtree. `--virtual-root PREFIX` blesses a prefix
as a sanctioned floor. `Core.Rx` is exempt (`--exempt Core.Rx`
in the recipe): it is refactor scaffolding, so it is neither a
subject of the report nor evidence for other placements. With `--virtual-root Core.Data` the B
residue is `Core.Equiv.Base` (`_≃_`, `iso→equiv`),
`Core.HLevel.Base.nType.∣_∣`, `Core.Transport.J.subst`, and
`Lib.Relation.Unary` (`Pred`, `∀[_]`): definitions with no shallow
public access that consumers across their namespace reach into. C
flags the `Core.Data.List` and `Core.Data.Maybe` facades for
re-exporting `Properties` and `Impl` lemmas whose only consumers
live under `Impl` (slack 1). These are measurements, not placement
verdicts.

Current library snapshot: 362 modules, 9666 definitions, 60074
edges, 0 unresolved references, 324 public re-export statements. Six broken leaf modules excluded
(`Data.Thin.{Category,Cover,Properties,Separated}` known debt, and
`Core.Coherence.Paths`, `Core.Path.Coherence`, the latter with a
scope error on `Core.Transport.Base.total-contr-unique`). Two facts
the tool surfaced in passing, both `verified` by reading the
source: `Cat.Logic.Base` imports `Core.Transport.Base
using (is-prop→PathP)` without using it, and
`Core.Groupoid.emb-equiv.retr` is a dead where-local.

Next: judge the B residue (bless floors with `--virtual-root`, add
facades, or move definitions) and the C facade rows. The excluded
modules rejoin the graph when their debt clears.

## 2026-08-04 — Bb.VirtualGraphs phase 2: the committed-source consolidation landed

**Slug:** virtual-graphs-vendor. Survey extended, twenty-nine
theorem and model modules of Agda landed, all `verified`.

Part 1: the plan's catalog extended to the four uncovered archive
trees (`Bb.WeakDeductiveSystem` core and Gist,
`Bb.NaiveVirtualGraph`, `Bb.OneTwist`, `Bb.VgCategoryShape`) —
§4.10–§4.14, two new hypothesis groups O (one-twist extraction) and
V (aligned chosen edge), three new duplicate clusters D18–D20. Full
row detail in `outputs/.drafts/virtual-graphs-vendor-survey-*.md`.

Part 2: `Bb.VirtualGraphs` grew from one module to thirty, committed
sources only (`Cat.Logic.*` entire plus the four archive trees;
`Test.*`-sourced rows deferred, including hypothesis groups E and F
and the `Monoid`/`Bool.Endo`/`Bool.Sleeve` and word/circle spike
models). Fifteen theory modules (`Stability` through `UnitShape`,
groups A/B/C/D/D′/P/X/H/O/V) and fourteen model modules (word,
circle island, Bool, path groupoid, abelian group). `verified`:
`gtimeout 300 just check <Mod>` exit 0 per module as it landed;
`just check-tree src/Bb` — 128 modules green; `just check Bb.index`
exit 0; no postulates, no `TERMINATING`, `virtual-graph` the only
record in the tree; `just lint changed` clean. No lemma omitted
anywhere. Source ↔ module mapping in
`src/Bb/VirtualGraphs/CHANGELOG.md`.

Next: a later pass vendors the `Test.*`-sourced rows once those
spikes are committed, and the remaining `Bb.NaiveVirtualGraph`
chosen-edge rows beyond `UnitShape` (plan §4.12 lists them).

## 2026-08-04 — Bb.VirtualGraphs opened: carrier landed, consolidation surveyed

**Slug:** virtual-graphs-vendor. Phase 1 of the virtual-graph
consolidation: survey and plan, one module of Agda.

`Test.NewDs.Carrier` ported to `Bb.VirtualGraphs.Type`, mathematical
content unchanged. Tree opened per the `Bb` contract (README,
CHANGELOG, `Bb.index` section). `verified`: `just check
Bb.VirtualGraphs.Type` and `just check Bb.index`, both exit 0.

Every result about a virtual-graph-shaped carrier across the
thirteen 2026-08-02/03 spikes, `Test.NewDs`, and `Cat.Logic.*` with
its fourteen `Gist` modules is cataloged in
`outputs/.plans/virtual-graphs-vendor.md`: 118 entries (74 general,
44 model-level) with `file:line` anchors, the minimal
hypothesis-telescope group each needs to be stated, and 17 flagged
duplicate clusters. Eleven hypothesis groups proposed, from the bare
carrier through framing, tower, readback, balanced, neutral,
natural, presentation, chosen-edge, reflexive-graph-dictionary, and
models, each a flat explicit telescope over the three-field carrier.
No record beside `virtual-graph` anywhere in the planned tree. The
torsor-correction rule is applied throughout: theorem statements
carry over, contaminated circle-verdict language does not.

Next: phase 2 writes the theorem modules per the plan's §6 layout,
gating each on a green checker run.

## 2026-08-03 — VG+DS: the torsor-criterion correction

**Slug:** vgds-torsor-correction. No Agda proof landed; correction
and consolidation only. Session log:
[`notes/2026-08-03-vgds-torsor-correction.md`](notes/2026-08-03-vgds-torsor-correction.md).

Lane identified a methodological error running through the whole
`Test.Spike*` circle-model sequence (`SpikeNeutralReadback` through
`SpikeGluingCharacteristic`): non-contraction of the recognized-pair
Σ at the circle was scored as flat candidate failure, when the
correct criterion is whether the free pairs form a torsor under the
group the canonical pair itself generates — literal contractibility
would demand that generator have no content. `unverified`: the
corrected criterion is stated only in prose, not yet a checkable
predicate. `blocked`: rewriting the five contaminated spikes'
verdicts (`SpikeCandidateGenerator`, `SpikeFramedShape`,
`SpikeEdgeCoherence`'s habitat prose, `SpikeGluingCharacteristic`'s
circle-clause reading, and the mediation trio's circle contractions)
on that criterion. `SpikeGradeSelector`, the eliminative arc, and all
word-model results are unaffected.

Also established, `Cat.Logic.Base`/`Type` (`virtual-graph` with
primitive `twist⁺`/`twist⁻`) is a proven dead end for the duploid
target (`src/Cat/Logic/TODO.md` item 7: balanced strength collapses
polarity) and is not adequate to the concept it names, despite being
machine-checked. `docs/deductive-systems/` deleted as premature
documentation of it. Retirement banners added to
`src/Cat/Logic/{lemmata,gloss,Base}` (statuses untouched, scope
narrowed). `verified`: `just check Cat.Logic.Base`, exit 0, after the
header edit. The full genealogy —
`Bb.NaiveVirtualGraph → Bb.WeakDeductiveSystem → {Cat.Logic,
Bb.OneTwist, Bb.VgCategoryShape}`, and today's recognition line's
place outside it — is in the session log, sourced from the `Bb/*`
READMEs.

Next: Lane pins the formal torsor criterion (session log §"Open
questions," item 1) before anything downstream — spike rewrites,
`Cat.Logic`'s vendoring into `Bb.*`, the `Cat.Logic.Gist.BalancedWord`
carrier/proof split — moves.

## 2026-08-03 — the gluing spike: the mixed-pair play, and the clause that over-excludes

**Slug:** gluing-characteristic. New `Test.SpikeGluingCharacteristic`,
verified (`just check Test.SpikeGluingCharacteristic`, exit 0, zero
warnings, no holes, no postulates; prose lint 1.36/100w).

States the pair grammar per ordered pair of objects (`cross`,
`sand`, the two fibers) with the gluing characteristic internalized
as clauses (`glue⁻`, `glue⁺`), final condition `pred`, level (c).
The transposed Kraus play closes (`grammar.play`): the gluing
clause manufactures the mixed diagonal sandwich, and the fiber
centers pin both components, so pair equality at the diagonal Σ is
GENERAL over a wild carrier. Consumption measured: (c) for the
mixed term, (b) for the anchors. The word model holds the condition
and contracts (`word.predᵂ`, `word.recoverᵂ`, `word.contractionᵂ`,
SHADOW, Nat rung). The general uniqueness theorem did not close:
off-diagonal inhabitants are parallel, not adjacent, and inhabitant
equality lacks condition-level rigidity (no `e-vs-I` transpose).
The crux computes emptiness, not freedom: the internal clause reads
every adjacent sandwich uniformly, so the circle refutes every pair
(`circle.no-predᶜ`, `circle.not-contrᶜ`, COUNTERMODEL) while the
level (b) freedom keeps its winding (`circle.freedomᵇ`, the ℤ in
the untwist slot). The sleeve confirms the characteristic across
the sleeve (`sleeve.glue-sleeveˡ/ʳ`), pins the components the
coherence was blind to (`sleeve.out-pins-d/c`), and then loses
everything to the empty direction: no recognition at all
(`sleeve.no-pred-ttᴱ`, `sleeve.no-recognizedᴱ`, BOOL-RUNG).

Verdict: the candidate fails, horn two. Mixing by internal clause
buys the play its term and over-excludes above the word rung.

Next: the wild probative instrument, with gluing carried as record
data, not demanded as a pointwise clause. The family-level play
(adjacent instances drawn from `recognized` itself) is the untested
route.

## 2026-08-03 — the edge spike: coh on the first two-object carrier

**Slug:** edge-coherence. New `Test.SpikeEdgeCoherence`, verified
(`just check Test.SpikeEdgeCoherence`, exit 0, zero warnings, no
holes, no postulates; prose lint 1.73/100w).

Builds the first instrument above the shadow: `ob = Bool`, both endo
homs and the connecting hom the word model's descriptors, the
reverse direction empty, reflection the word sandwich everywhere.
The whole committed record instantiates (`deductiveᴱ`), and
`cross-reads` realizes the mis-split by `refl`: a connecting
instance reads `true`'s negative component and `false`'s positive
component.

Measured rows: the diagonal pins per object (word pinning), so
`is-framed` is a proposition for the boring reason (`framed-prop`).
`coh`, the off-diagonal residue (`residue`, `rb-residue`), is blind
to the two components it does not read (`coh-blind`) and pins the
two it does read (`coh-pins`, recognition strength, no tier). The
census perturbations at `false` (ω̂, ε̂, δ̂ in the negative slot)
all pass `coh` and all fail flanks. The interesting case is empty:
the diagonal at both objects implies `coh` (`diag→coh`). Transposed
play: the GENERAL content is sandwich agreement (`play.agree`); the
Bool-rung closure gives one component per object (`play-pins`); the
far components are provably free (`snd-free`, `fst-free`). Seat
verdict: option (ii), `coherent R = rbᶠ (frame-of R)` beside the
framing (`amended.is-coherent-deductive-system`), conservative at
this instrument (`complete`, `strip`). New tag BOOL-RUNG in use.

Pragma note: `--cubical`, by Lane's call this session. The committed
shape and the pinning live in `--cubical` modules, and an
`--erased-cubical` importer gets their names only erased (probe
recorded `DefinitionIsErased`).

Next: the wild probative instrument, with a sharpened brief. `coh`
constrains only the outer components, so the wild carrier must
measure what pins the inner two.

## 2026-08-03 — the shape spike: is-framed in Kraus's grammar

**Slug:** framed-shape. New `Test.SpikeFramedShape`, verified
(`just check Test.SpikeFramedShape`, exit 0, zero warnings, no
holes, no postulates; prose lint 1.96/100w).

Commits the candidate record over the bare carrier (`ob`, `hom`,
`reflect`): `pair`, `is-twist = flanks × (inv⁻ᵗ × inv⁺ᵗ)`,
`is-framed = (x : ob) → Σ (pair x) is-twist`, and
`is-deductive-system = is-stable × Σ is-framed cuts`, with the cuts
as contractible reflect-fibers over the reframed carrier.
Factorization verdict: the sandwich is mis-split per object (each
instance reads two pairs), so `is-twist` keeps the diagonal
(endo) fragment, and the off-diagonal residue is the multi-object
coherence question (Bool rung, open).

Verified rows: word model instantiates the whole record, pair forced
to `(τ̂ , ε̂)` by flanks alone, `is-framed` a proposition
(Kraus's chain), cuts definitionally the model's compositions,
`associates (τ̂ , ε̂ , ε̂)` still failing. Circle instantiates too,
but the recognized pairs form a circle: Σ not contractible,
`is-framed` not a proposition, uniqueness refuted at an
invertible-framing carrier. `cancel⁻`/`cancel⁺` transpose Kraus's
neutrality derivation and yield `unitr⁺`/`unitl⁻` through
`tower.unital` (GENERAL); the idem⁻ rung holds and the chain does
not complete. Pre-duploid checklist: three associativities and the
four closure lemmas PROVED over the recognized cuts; Prop. 4
profunctor CITED as target; clause-4 neutrality the declared
departure.

Next: the wild probative instrument (distinct twists, failing
associates, wild homs). It settles which branch of the uniqueness
question is forced.

## 2026-07-29 — session close: the polarity collapse, reviewed and vendored

**Session log:** [`notes/2026-07-29-polarity-collapse-and-vendor.md`](notes/2026-07-29-polarity-collapse-and-vendor.md).

Closes the session that produced the five entries below (h-level,
twist-condition, collapse, operator-carrier, readback-shift), their
three-reviewer adversarial audit, and the vendor pass. Adds one thing
not yet in an entry of its own: a staleness diagnosis in
`src/Cat/Logic/TODO.md`. A new "Stale in light of the polarity
collapse" block, plus pointers from investigation items 4 through 7.
Lines 6 (shifts as representability) and 7 (the reflection theorem, a
deductive system's polarized, balanced core is a duploid) are
`blocked`, not merely open. Balance is exactly the strength at which
`PolarityCollapse` proves polarity collapses, so no polarized-and-
balanced core exists to build a duploid from. Item 4's "subcategories"
line closes the same way. Items 1, 2, 3, 5, 8, 9 stand unaffected. The
earlier RULED note against primitive polarity rested on a clause now
known false. Reopening it is Lane's call, recorded for the next
session rather than decided here.

`verified`: all five promoted modules check individually, plus
`just check-tree src/Cat/Logic/Gist` (14 modules) and the whole-library
`just check-tree`, which is clean except six pre-existing failures
unrelated to this session (`Core.Coherence.Paths`,
`Core.Path.Coherence`, `Data.Thin.{Category,Cover,Properties,
Separated}`). A stale import and unrelated unsolved metas cause them;
none of the affected files were touched. `just lint changed` clean,
zero holes or postulates across the session's modules. `blocked`:
`readback-square` in general. `inferred`, not `verified`: the
staleness diagnosis is a consequence-drawing pass over already-
verified results, not a new checker run.

---

## 2026-07-29 — the polarity chain promoted into Cat.Logic.Gist

**Five modules are live**: `Cat.Logic.Gist.PolarityHLevel`,
`Cat.Logic.Gist.PolarityTwist`, `Cat.Logic.Gist.PolarityCollapse`,
`Cat.Logic.Gist.OperatorCarrier`, `Cat.Logic.Gist.ReadbackShift`.
Promoted from their `Test.SpikeXxx` originals, `just mv` in
dependency order, one module checked before the next rename. Slug
`vendor-polarity-gists`, brief at
`outputs/.plans/vendor-polarity-gists.md`.

Three adversarial reviews covered the first three spikes. They found
the underlying mathematics sound, one wrong citation, and several
overclaiming or underclaiming prose passages. The promotion applied
the fix list alongside each rename.

`PolarityHLevel`: the `positive`/`negative` citation no longer names
Definition 1 of `resources/munch-maccagnoni-duploids`, a primitive
partition map and not this transcription. It now names Clairambault
and Munch-Maccagnoni's Polarity definition, *Duploid situations in
concurrent games* (GaLoP XII, 2017), at
`resources/mmmm-classical-notions/article.tex:1694-1700`. `shiftP`
and `shiftN` renamed `shift⁺` and `shift⁻`, the house convention for
hand-marked names.

`PolarityTwist`: `positive-from-unit` and `negative-from-unit`
localized to the one object their proof terms actually use. Two new
lemmas, `positive-empty` and `negative-empty`, make the word model's
vacuous two-edge check machine-checked. `linear-refuted` and
`thunkable-refuted` join the import list. A new sentence states the
`gen-diag` scope limit: the generated-carrier tier is vacuous off a
loop edge. The closing prose notes the `positive`/`negative`
duplication against `PolarityHLevel` and leaves it for a later pass.

`PolarityCollapse`: a new `from-deductive-system` module restates
both collapse directions at the bundled `is-deductive-system` record,
not only at the raw tiers. "One property"/"one predicate" now reads
"logically equivalent" (the module proves a two-way implication, not
identity of the two predicates). `split-refuted` and
`split-refuted-dual` had byte-identical signatures despite naming two
distinct facts. Sharper replacements, `no-positive-split` and
`no-negative-split`, each use only the two hypotheses they need.
"Category" now reads "unital magmoid", this repository's term for
the same untruncated-hom structure. Two sentences overclaiming
necessity now match the module's own "It could instead drop..."
qualifier. The scaffolding simplification the reviews noted
(`centre`, `cross⁻-into`, and `twist⁻-centre` are provably
unnecessary) is deliberately not attempted this pass.

`OperatorCarrier` and `ReadbackShift`: rename only, completed after
the review batch. Their imports of `PolarityTwist` and
`OperatorCarrier` came through the `just mv` sweep correctly.

Ledger updated (`src/Cat/Logic/TODO.md`). Every `Test.SpikeXxx`
reference now reads `Cat.Logic.Gist.Xxx`. The h-level block's
citation matches the module's fix, and the twist block gained the
duplication note. `outputs/.plans/polarity-hlevel.md` corrected for
consistency.

`verified`: `just check` on each of the five modules individually,
zero warnings, no holes, no postulates. `just check-tree
src/Cat/Logic/Gist` clean, 14 modules. `just check-tree` over the
whole library reports the same six pre-existing failures as before
this session, under `Data.Thin` and `Core.Coherence`/`Core.Path`.
The causes are a stale `Cat.Type` import and unrelated unsolved
metas, neither touched here. `just lint changed` passes. `rg -n
"Test\.Spike(PolarityHLevel|PolarityTwist|PolarityCollapse|OperatorCarrier|ReadbackShift)"
src/` returns nothing.

## 2026-07-29 — the readback torsor stops at the presentation

**`Test.SpikeReadbackShift` is live** (slug `readback-square`, brief
at `outputs/.plans/readback-square.md`). The carrier spike below left
`readback-square` open. It named `Cat.Logic.Gist.ReadbackTorsor` as
the only instrument that varies a readback over wild homs. This spike
measures what that instrument reaches. It refutes nothing. At the
circle model the square holds, at both readbacks.

The readback is free structure. `is-deductive-system` names `reflect`
and the two twists, and never the readback. So `retune-axioms` carries
every tier's witness across a change of readback, with no proof. That
gives two deductive systems over the circle model which differ in the
readback alone, `rb₀` and its one-winding shift `rb₁`.

The presentation does not follow. Six components return on the nose,
and `assoc` returns up to a path through stability. `cross-pivot` and
`unitr` each gain one winding and do not return
(`cross-pivot-differs`, `unitr-field-differs`). The carrier returns on
the nose, so no identification of the two presentations holds the
carrier fixed. There is no refuting pair.

The square's two sides move together. Every word the round trip writes
at the axiom is a loop at `base`, and that loop space is commutative.
The shift is then a signed count of readback occurrences. The derived
readback gains two windings and one uncomputed loop `κ₀`, and the
reflection square against the field gains the same. `square→` and
`square←` transfer the square across the retuning.

At the circle model the square reduces to the triviality of the mixed
associator at the axiom. That holds, because the model reads the
positive cut witness through `mult-assoc base`. So `square₀` and
`square₁` hold, and `round-graph` closes the graph round trip at each
readback. No truncation enters: the circle is a groupoid and not a
set, so the square is a proposition and not a triviality.

Ledger updated (`src/Cat/Logic/TODO.md`, the readback-torsor block).
`verified` (`just check Test.SpikeReadbackShift`, 2026-07-29, zero
warnings, no holes, no postulates). Next: `readback-square` in
general, which needs the same cancellation without a commutative loop
space, and without a cut witness that degenerates at the axiom.

## 2026-07-29 — a deductive system as a category with one operator

**`Test.SpikeOperatorCarrier` is live** (slug
`category-operator-presentation`, brief at
`outputs/.plans/category-operator-presentation.md`). The collapse
spike below rewrote every negative cut through one operator. This
spike states the carrier that rewriting leaves, and measures how far
it reaches. The structure of a deductive system is a wild category
with one endo-operator. The axioms are not.

`presentation` is the record: `unit`, `_⨾_`, `assoc`, `unitl`,
`unitr`, the operator `cross`, a second endo-edge family `pivot`, and
three laws. Each law is a theorem of a deductive system (`pair⁻`,
`cut⁻-cross` against `unitr⁻`, `cross⁻-cut⁺`), and the backward
direction consumes every field. `op-cross` shows `opᴰ` exchanges the
two readings of the operator on the nose.

Backward, `carrier.graph` is a virtual graph with readback and no
hypothesis: `reflect f γ` is the flanked word `(cross s ⨾ f) ⨾ k`.
All four tier fibers are inhabited, and readback forces each fiber's
edge. What is missing is `residue`: stability, plus one
propositionality demand per invertibility fiber. `hom-sets→residue`
discharges it, so a presentation with hom sets is a full deductive
system. Over wild homs the residue stands open, neither derived nor
refuted.

Both round trips are componentwise, and two components return only up
to a path. `cross` returns up to `unitr`, and `reflect` up to
`round-reflect`. The record-level identity of graphs is exactly one
square, `readback-square`, from which `round-graph` and `round-system`
derive both records.

The dictionary reads `associates`, `thunkable` and `linear` as the
commutation defect of the operator. Polarity becomes
representability: the operator on `hom(-, x)` is right multiplication
by one edge, forced to be `cross⁻ (twist⁺ x)`.

Ledger updated (`src/Cat/Logic/TODO.md`, the carrier block).
`verified` (`just check Test.SpikeOperatorCarrier`, 2026-07-29, zero
warnings, no holes, no postulates). Next: the readback square, and
whether the residue admits a countermodel over wild homs.

## 2026-07-29 — polarity does not split at full strength

**`Test.SpikePolarityCollapse` is live** (slug
`polarity-distinguishing-model`, brief at
`outputs/.plans/polarity-distinguishing-model.md`). The brief asked
for a deductive system with one positive object and one negative
object. No such system exists. The two twist conditions at an object
are equivalent. So `positive` and `negative` are one predicate, and no
carrier separates them.

The proof reads the framing as a category plus one operator. `assoc⁺`
with its two unit laws makes the edges a category whose identity is
`twist⁺`. `mixed-assoc` with `unitl⁺` rewrites `f ⨾⁻ g` as `(f ⨾⁻
twist⁺) ⨾⁺ g` (`cut⁻-cross`). A linear `twist⁺ x` pins that operator
to one positive cut against a right inverse of `twist⁻ x`. The
operator then passes through every positive cut at `x`, which is a
thunkable `twist⁻ x` (`from-linear`).

`from-thunkable` runs the dual. `split-refuted` closes the brief's
four clauses, and `word-check` derives each of the word model's two
refutations from the other.

A finite-model search preceded the proof and agrees with it
(`outputs/.notes/polarity-distinguishing-model-search.py`). Take the
two-object carrier whose hom sets are its two twists, with no edge
back from the second object. Exactly four deductive systems exist
there. All four are group-like, and both polarities hold at both
objects in each one.

Ledger updated (`src/Cat/Logic/TODO.md`, collapse
block + line 4). `verified` (`just check Test.SpikePolarityCollapse`,
2026-07-29, zero warnings, no holes, no postulates). Next: a stratum
where the polarities differ drops one of the consumed laws. The
candidates are the mixed law, one hand's associativity, and the
invertible framing.

## 2026-07-29 — the duploid papers, reviewed and one of them audited

**`munch-maccagnoni-duploids` is `verified`: 29/29 CONFIRMED
(digest-level).** Ten revision rounds, seven adversarial reviews, and
one independent statement audit, converging on a tracked correction
patch and a committed measuring script (`pdf-scan.py`) that turns
every drawn-mark count in the entry into a `--check`-verified one
instead of an asserted one. The audit's own find, not caught by any
review: the Theorem 28 digest's reflection triangle was mirrored,
traced to two wrong `ToUnicode` font maps inside the PDF itself, fixed
and disclosed. `just resources-verify` now lists the entry
`audited — load-bearing capable`, up from `NOT audited`.

**`mmmm-classical-notions` is `unverified`, mid-cycle.** A researcher
pass and merge raised its digest coverage from 6/44 to 24/44 main-text
statement environments (7 to 30 Content digests). Its own review-2
findings (one MAJOR — `bin/resources-verify` cannot parse a
`Statements verified: N/M` fraction, so a 3/30 entry reads as fully
audited — and seven MINOR) are recorded but not yet applied, and no
audit has run over the 23 new digests.

Committed: `resources/munch-maccagnoni-duploids/README.md`,
`resources/munch-maccagnoni-duploids/pdf-scan.py`,
`outputs/duploids-entry-audit.md`. Session log:
[`notes/2026-07-29-duploid-papers-audit.md`](notes/2026-07-29-duploid-papers-audit.md).

## 2026-07-29 — mmmm-classical-notions closes out, both duploid entries vetted

**`mmmm-classical-notions` is `verified`: 30/30 CONFIRMED
(digest-level).** Review-2's revision plan landed. The Vetting section
now discloses a second source typo. The digest preamble names the
`⟑`/`⟇` substitution, and two digests fix `M` to `ℳ`. The Section map
gains the `l.3725` `\end{document}` line and the source's own names
for Joyal's obstruction theorem and §13.

The Dialogue duploid digest's `≃` and the dropped clause in the
Thunkable-implies-central digest are both restored. An independent
audit (Claude, Opus 5) then re-derived all 30 digests from
`article.tex`, from scratch. It confirmed 23 near-verbatim and 7
paraphrase digests, zero not confirmed, including the six passages the
revision touched.

**`bin/resources-verify` now parses the `Statements verified: N/M`
fraction.** It reports a partial standing when `N` is less than `M`.
It reads the "N confirmed on first pass, K corrected" phrasing as full
coverage, not partial. `resources/README.md` now names a digest
addition or revision, beside a re-fetch or a re-extraction, as an
event that voids the field.

**Both duploid-tier entries carry a `Vetted:` line, at Lane's
direction.** `munch-maccagnoni-duploids` (29/29, from the prior
session) and `mmmm-classical-notions` (30/30, this session) both
retire their PROVISIONAL marker.

Uncommitted, pending Lane's go-ahead:
`resources/mmmm-classical-notions/README.md`,
`resources/munch-maccagnoni-duploids/README.md`,
`resources/README.md`, `bin/resources-verify`,
`notes/2026-07-25-two-lineages.md` (the downstream anchor fix from
review-2), and `outputs/classical-notions-entry-audit.md`. Session
log: [`notes/2026-07-29-classical-notions-audit-complete.md`](notes/2026-07-29-classical-notions-audit-complete.md).

## 2026-07-29 — polarity is a twist condition, at two strengths

**`Test.SpikePolarityTwist` is live** (slug
`polarity-twist-condition`, brief at
`outputs/.plans/polarity-twist-condition.md`). The spike measures
the converse of the forward instantiation: whether linear twists
at `x` return `positive x`, and thunkable twists `negative x`.

All four closures check over the bare tower, from the three
associativity theorems alone: `thunkable` and `linear` under both
cuts. Two are one-sided (`linear-⨾⁺` reads its leading factor,
`thunkable-⨾⁻` its trailing factor). The converse follows at two
strengths. On carriers generated by the twists under the cuts
(`gen`), both twists decide the polarity. At full deductive-system
strength the balanced unit laws make one twist decide it, so no
deductive system separates the twist condition from the polarity.
`gen-sem` proves the word model generated, where the check is
vacuous: each hypothesis pair fails on exactly one twist.

Open: the twist reduction below invertibility on non-generated
carriers. A countermodel needs a stable, composable,
non-invertible carrier with both twists linear at an object and a
non-linear edge out of it. Ledger updated
(`src/Cat/Logic/TODO.md`, twist-condition block + line 4).
`verified` (`just check Test.SpikePolarityTwist`, 2026-07-29, zero
warnings, no holes, no postulates). Next: either construct that
countermodel or take up the polarity subcategories from line 4.

## 2026-07-29 — the h-level of polarity, at two models

**`Test.SpikePolarityHLevel` is live** (slug `polarity-hlevel`,
brief at `outputs/.plans/polarity-hlevel.md`). `positive` and
`negative` transcribe the duploids paper's Definition 1 over the
tower, with no truncation.

Circle model: `mult-assoc` makes every
edge thunkable and linear, so both polarities hold at the one
object. The `rot`-shift gives a second witness one winding away.
So polarity is structure: not a proposition, not contractible.
`filler-distinct` shows two positivity witnesses fill one
`associates` cell in two ways. A positive-objects subcategory
therefore carries its mixed associator as a choice.

Word model: both polarities are propositions over the set-level
homs, and both are empty (`linear-refuted` at `ε̂`,
`thunkable-refuted` at `τ̂`). `verified`: `just check
Test.SpikePolarityHLevel`, 2026-07-29, zero warnings, no holes,
no postulates, prose at 0.19/100w.

Ledger updated: `src/Cat/Logic/TODO.md` gains the settled block
"the h-level of polarity, at two models". Line 4 of the
investigation list points at it. The RULED note on mode
separation stands untouched. Open next: the polarized
subcategories and the closure of `thunkable`/`linear` under the
compositions (line 4's remainder).

## 2026-07-29 — the defect promoted, and the Cat.Logic ledger split starts

**`Cat.Logic.Gist.AssociatesDefect` is live.** Promoted from
`Test.SpikeAssociatesDefect`: `just mv`, then a rewritten opener
that leads with the result's significance instead of the bare
statement. `verified`: `just check
Cat.Logic.Gist.AssociatesDefect`, zero warnings, no holes, no
postulates, prose at 1.50/100w.

Every stale reference to the old name swept from `TODO.md`, this
file, and `outputs/.notes/associates-defect-results.md`. A
repository-wide search confirms none survive.

**The `Cat.Logic` ledger split starts**, per
`docs/plans/documentation-restructuring.md`. New:
`src/Cat/Logic/lemmata.md` (bare statement and citation) and
`src/Cat/Logic/gloss.md` (extended commentary), same numbering as
`docs/gloss.md`.

T25 to T30 and T32 to T35 moved out, T36 added for the new result.
T31 and T21 to T24 stay in `docs/gloss.md`. Their citations resolve
to archived `Bb` modules with no ledger of their own yet. The plan
document now records this as the open remainder of step 4.
`verified`: `just lint citations` finds zero dangling citations in
the two new files, and `just lint changed` passes clean.

**Process note.** A subagent stopped by Lane mid-run does not
resume through `SendMessage`. It returns `success: false` and
requires an explicit relaunch. A subagent that pauses itself
resumes fine. Recorded in the `restart-means-same-agent` memory
file.
Session log: [`2026-07-29-associates-defect-promotion.md`](notes/2026-07-29-associates-defect-promotion.md).

## 2026-07-29 — the associates defect is a framing word, per flanking edge

**The bare independence is now a measured defect.** Over the free
balanced point (`Cat.Logic.Gist.BalancedWord`), each bracketing of
`associates` determines the other up to a twist word, one word per
hand, and the word reads one flanking edge alone. `defect⁺`
corrects on the leading side by `w⁺ (rise f)`. `defect⁻` corrects
on the trailing side by `w⁻ (zrunW h)`. Both hold at every triple.
The corrections are powers of the reverse bicyclic composite, and
they are units exactly at the thunkable/linear closures. No
uniform word exists in any of the sixteen placements, and fourteen
placements fail outright. The winding grade never separates the
bracketings (`shift-associates`), so the two-sided-cancellation
collapse erases the defect. `verified`: `just check
Cat.Logic.Gist.AssociatesDefect`, zero warnings, no holes, no
postulates. The placement census and the ℤ-collapse sample are
script-level (`outputs/.notes/associates-defect-*`). The scope is
the free point itself. The verdict sits in `src/Cat/Logic/TODO.md`
under the settled profile block. Next step: the generator-bearing
word model (initial-model program, item 1 sequels), to test the
per-edge factorization beyond the point.

## 2026-07-29 — the audit chain refuses, and documents get registers

**Three passes, a defect at each.** A source-fidelity certification on
`resources/munch-maccagnoni-duploids/` was written and certified by
one pass in one run, which `resources/README.md` forbids. An adversarial
`reviewer` at opus/xhigh found six of 24 digests drifting, coverage at
24 of the paper's 28 statements, an invented citation ("after Führmann
and Hasegawa" where the source says `[16,8]` and Hasegawa appears
nowhere in the paper), and a **fabricated evidence claim**: "confirmed
against rendered PDF pages" for a paper with no vendored PDF and no
LaTeX engine installed. `verified` by the lead re-deriving each. The
field was **withdrawn**; `just resources-verify` now reports the entry
`NOT audited`. Lane's diagnosis of the Hasegawa error held and was
narrow: exactly one contamination hit, borrowed from the sibling entry
whose title carries that name, digested in the same run.

**The lead then corrected six digests and wrote four missing ones, and
a third pass refused the field on two defects in those corrections.**
The instructive one: the text extraction flattens a two-column display,
the lead read it in line order, and Proposition 16's `⇑f` lost its
`force_A` while `⇓f` gained one. The result typed as `A → ⇑B` where the
functor needs `⇑A → ⇑B`. Settled by a 500 dpi render and the type of
`force_P`. `verified`: 26 of 28 digests faithful, both wrapped anchors
correct, coverage 28/28. `unverified`: Propositions 14 and 16 as now
written. `blocked`: the field, pending a fourth reader over those two
only — the 26 confirmations stand.

**Tooling.** `just sync` and `just check-all` retired with the All
aggregator, references struck from five files. `bin/lint` gains a
`citations` check: every module a `gloss.md` or `lemmata.md` names must
resolve under `src/`. Opt-in until the ledger split lands. `verified`
against false positives with a planted ledger.

**Ruling (Lane): four registers, and `docs/plans/`.** Module prose says
what an object is; `<namespace>/gloss.md` carries commentary on a
construction; `<namespace>/lemmata.md` the statements; `docs/guidelines/`
standards stated abstractly. `gloss` and `lemmata` are the classical
pairing — headword and commentary. Separately, standing plans with
gates get `docs/plans/`, distinguished from `outputs/.plans/` by
ephemeral against standing rather than tracked against untracked: every
file in the latter today is a consumed run brief. `composite-rx-refactor`
was never misplaced, being a standing gated program like the roadmap;
what was wrong in `docs/` was `deductive-systems/`, namespace commentary
belonging beside its code.

The cause of all of it: `just mv` sweeps `src/` only, nothing typechecks
a document, so a document naming a module inherits its lifetime without
its maintenance. Thirteen of `docs/gloss.md`'s 22 cited paths dangle.
Session log:
[`notes/2026-07-29-audit-chain-and-doc-registers.md`](notes/2026-07-29-audit-chain-and-doc-registers.md).

## 2026-07-28 — duploid source audit: both entries cleared to load-bearing

**Statement-level audit of both duploid papers in `resources/`**, run
via `/deepresearch` (2 parallel `researcher` subagents, then
`verifier`, then `reviewer`, then a revision pass). `verified`:
`mmmm-classical-notions`'s seven existing Content digests, 7/7,
against `article.tex`; `munch-maccagnoni-duploids`'s 24 numbered
statements, 24/24, against `duploids.pdftext` — this entry had no
digests before this pass, now does. Two source-level errors found in
the papers themselves: a codomain typo in `mmmm-classical-notions`'s
composition-law diagram (`article.tex:1531`), and a
"linear"/"thunkable" slip in Munch-Maccagnoni's Proposition 8 proof
(`duploids.pdftext:434-436`).

**Correction, 2026-07-28.** This entry read "confirmed against
rendered PDF pages, not extraction artifacts". That is withdrawn for
the `mmmm-classical-notions` typo. No PDF of that paper is vendored
and no LaTeX engine is installed, so no rendered page could have been
read. The finding stands on the vendored `article.tex`, which is
LaTeX source, so no extraction step exists to blame. The
Munch-Maccagnoni finding is confirmed against a rendered page, and a
second reviewer strengthened it: `duploids.pdftext:703-704` shows the
paper's own later text reading Proposition 8 as the audit does. The
same wording stands uncorrected in the commit message of `2611d7e`,
which cannot be edited.

**`24/24` qualified, same date.** A second review at higher tier
(`outputs/.drafts/duploids-statement-audit-review-2.md`) found three
of the 24 `munch-maccagnoni-duploids` digests misstating the source,
one by attributing the thunkable terminology to an author the paper
never cites. Twenty-one of 24, and all seven mmmm digests, were
re-read and confirmed faithful. The cause is structural:
`resources/README.md` defines the field as an independent audit
dispatched after the entry is built, and this pass wrote the digests
and certified them in one run. `mmmm-classical-notions` keeps `7/7`.
`munch-maccagnoni-duploids` reads as audited with corrections
pending until a second reader re-issues the field. `docs/gloss.md`
T35 is unaffected: its cited digests are among those confirmed.
`unverified`, flagged open rather than asserted: whether
`mmmm-classical-notions`'s duploid definition actually coincides with
either of Munch-Maccagnoni's two equivalent forms — the paper itself
concedes only "a slight variant of" (`article.tex:1817`). The
`reviewer` pass found four MAJOR issues (a wrong citation inventory,
an incomplete comparison space, a false "no dead anchors" claim, an
uncorrected error in a supporting research file) and three MINOR; all
fixed in a revision pass and independently re-verified on disk before
delivery.

**Barrier removed.** `Statements verified:` fields written to both
`resources/mmmm-classical-notions/README.md` and
`resources/munch-maccagnoni-duploids/README.md` (the latter also
gained its first Content digests section); `just resources-verify`
now reports both "audited — load-bearing capable" (was "NOT
audited"). `TODO.md`'s "the two duploid source audits" line checked
off.

Session log:
[`notes/2026-07-28-duploids-statement-audit.md`](notes/2026-07-28-duploids-statement-audit.md).
Next: a future pass on whether `mmmm-classical-notions`'s
universal-property duploid definition is equivalent to
Munch-Maccagnoni's Definition 7 (the more likely bridge, per the
audit).

## 2026-07-28 — the euler subagents: models pinned, skill access repaired

**Models pinned** (Lane). No agent in `.claude/agents/` set `model:`,
so all four inherited the session model and would drift together on
any change of default. The euler pipeline runs researcher, writer,
verifier, reviewer, and that ordering decides the tier. An agent with
a checker downstream can run cheaper. An agent that is itself the
last check cannot. `researcher` and `writer` take `sonnet`.
`verifier` takes `opus`, effort raised `medium` to `high`, since its
transcription diffing against dependent types fails silently.
`reviewer` takes `fable`.

**Skill access was broken, and with it a contract duty.** The
`skills:` frontmatter key is absent from the documented field set,
and no shipped agent anywhere uses it. All four euler agents declared
`skills: - writing` and none had the `Skill` tool, so none could
invoke the skill. `.claude/rules/euler.md` requires the verifier to
run the writing skill's linter on the final artifact and record the
score in the `.provenance.md` sidecar. That duty was
undischargeable. All four now carry `Skill` in `tools`, plus a
role-specific prose-standard section. The verifier's section names it
owner of the prose gate.

`verified`: the frontmatter of all four parses, each carrying
`model`, `effort`, `Skill` and a prose section. Linter scores
improved on all four prompts (3.32→3.13, 3.55→2.94, 4.04→3.73,
4.76→4.48). `unverified`: that the harness honors `model: fable` in
frontmatter. The Agent tool's enum accepts it, but the plugin-dev
doc lists only inherit/sonnet/opus/haiku and may predate Fable.
`unverified`: that `skills:` does anything, and that any of this
takes effect, since agent definitions load at session start.
`inferred`: that each model suits its role. One data point per model
this session, and nothing compares Opus against Fable for
adversarial critique. Next: smoke-test the reviewer, then return to
`Cat.Logic.Morphism`. Session log:
[`notes/2026-07-28-euler-subagent-config.md`](notes/2026-07-28-euler-subagent-config.md).

## 2026-07-28 — morphisms opened, a polarity alarm answered, the doc set reconciled

**Initiality landed, `verified`** (`Test.SpikeMorphismInitial`,
recorded `just check`, zero obligations): the morphism record
(`map`, `hmap`, `pres-twist±`, `pres-reflect`) and
`is-initial G = ∀ G' → is-contr (G ⇒ G')`, itself a proposition.
Initiality truncates no hom. It asks one fiber to be contractible.
The empty graph is initial. The codiscrete graph on two points
carries the full axioms and still has two distinct self-maps, so no
axiom makes system maps a proposition. `Cat.Logic.Morphism` did
**not** land. The polarity report stopped both agents, and T1 had
written nothing.

**The reported polarity error was a false alarm with a real cause.**
`inj⁺`/`inj⁻` and the whole composition register carry correct
labels, and no proof moved. The missing fact was the order
convention. Munch-Maccagnoni composes applicatively and this library
diagrammatically, so transcribing Definition 1's (•◦) clause without
reversing the order reads the word backwards. That inverts the
labels on sight. `verified` that `(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)` is
that clause verbatim, so `⁻ = ◦` and `⁺ = •` both stand. The
convention now sits in `towers.md` and the TODO.

**What did cause it: prose that justified a label by the held
axiom.** Four sites said "coact holds `var`, hence…", which reads as
binding `var` to coactions and inverts the standard. All corrected.
Ruling (Lane): `act` and `coact` keep their names, since the types
force that binding, making it implementation and not semantics.
`framing.md` now derives the framing gloss from traced crossings
(`twist⁺` a buffer, `twist⁻` a future), `CONJECTURED`, since
*Asynchronous Games 3* is still not vendored.

**Docs debt paid, not deferred** (Lane: "we do pay for docs debt
like this"). Eleven of twelve `docs/deductive-systems/` files were
stale against the record cut. `the-package.md` carried the pre-cut
three-field record and cited `FramedCut` as inhabitant, which
readback rules out. `composability.md` showed the stability-indexed
record. `towers.md` claimed one unit law per hand, now four.
`invertibility.md` and `framing.md` each claimed nothing decides
whether a centre is the other twist, which T33 refutes.
`README.md` omitted `readback` entirely. The retired `pin`, `K`,
`unital` and `absorption` names left `docs/` and
`Cat.Logic.Type`'s register list.

**`(D′)` retired** (Lane). It named a position only against the
rejected `(C)` and `(D)`, so it read as a variant when it is the
definition. Live prose and `docs/roadmap.md` now say "deductive
system". The TODO keeps the letters as the record of the decision.
`Cat.Logic.Gist.BalancedWord` opens with the construction instead.

`verified`: `check-tree src/Cat` 21/21, `check-tree src/Test` 9/9,
`lint changed` clean, all twelve doc files and `roadmap.md` at or
under the 2.0 prose gate. `unverified`: the morphism signature's
implicit/explicit calls (elaboration probes unrun) and
`pres-⨾⁺`/`pres-⨾⁻` (unattempted). Next: `Cat.Logic.Morphism` from
`outputs/.plans/system-morphisms-T1.md`, then promote the spike to
`Cat.Logic.Gist.MorphismInitial`. Session log:
[`notes/2026-07-28-morphisms-polarity-docs.md`](notes/2026-07-28-morphisms-polarity-docs.md).

## 2026-07-28 — the free balanced word model: the (D′) profile closes, refuted

**The oracle ran, `verified`** (`Test.SpikeBalancedWord`, 948
lines, recorded `just check`, zero obligations): the word model
of the bare framed point at (D′) strength — normal forms as
eventual-translation descriptors, cuts admissible, no quotient,
decidable equality, the full two-field instance. `associates
t⁻ t⁺ t⁺` is refuted, so generic `associates` is underivable at
(D′): the profile is exactly pre-duploid plus `mixed-assoc`, the
four unit laws, and the twist-flanked family. Bound for the
inhabitants line: `t⁻` not thunkable, `t⁺` not linear. The
winding conjecture holds: endo-homs ℤ-graded by the shift, the
double twist the `+1` generator, the obstruction exhibited as
one-sided invertibility (`refl` one way, refuted the other).
`inferred`, not proved: the model is the free object (empirical
certification 64/64 through six leaves,
`outputs/.notes/balanced-word-model-*`); initiality is line 9
items 2–3.

**Test distributed under spike zero, the archive got its
process, `verified`**: twelve chosen-edge spikes →
`Bb.NaiveVirtualGraph`; `Cat.Depreciated` (49) →
`Bb.CatsWithExplicitInterchange`, its twelve Test witnesses →
its `Gist` (gloss T21 now cites checked code); the Magmoid suite
→ `Bb.UnitalMagmoids`; `src/Bb/CLAUDE.md` process, READMEs,
CHANGELOGs, `Bb.index` — `src/Bb` 98 of 98, `src/Test` 9 of 9,
four removals with grounds, `CatData` resolved as a planning
name never adopted. Rulings executed: width 100 everywhere,
`check-tree` sweeps `.lagda*`. The whole-tree sweep surfaced six
pre-existing reds (the `Data.Thin` four, `Core.Coherence.Paths`,
`Core.Path.Coherence`), itemized in the root `TODO.md`. Whole
tree: 317 of 323. Lint clean.

**Close-out, `verified`**: the spike's general lemmas vendored
home (`So` to Bool, the comparators bridged to builtins in Nat,
`DecEq-List` generalized, the Int kernel with `_⊖_`), the spike
promoted to `Cat.Logic.Gist.BalancedWord` (`src/Cat` 21 of 21,
`src/Core` 137 of 139, the two failures pre-existing). Root
`CLAUDE.md` rewritten to the `writing` skill (6.01 → 1.45 per
100 words) with the Delegation section and the prose-law
priority; the root `TODO.md` opened; the roadmap re-founded (the
foundation track under project 1, the Core reformation gated as
project 2). Commits: `4dd6bd0`..`cfc2147` (the ten), then
`d2c6499`, `7436984`, `e57dce1`, `47a7033`, and the notes
commit.

Next: line 9 item 2 (morphisms), the gloss entries for the cut
and the profile. Log:
[notes/2026-07-28-balanced-word-model.md](notes/2026-07-28-balanced-word-model.md).

## 2026-07-28 — Cat.Logic: line 2 settled, the Gist namespace, the balance dossier, custody

**Thunkability is data, `verified`** (`Cat.Logic.Gist.ThunkableSquare`,
checked): the length-4 square `compat` stated, and the circle model
refutes propositionality of `thunkable` and of the square-refined
closure in a full weak system. The freedom is a loop-space action and
uniform shifts are natural, so no coherence tower truncates it. The
same mechanism forecast the balance torsor, `verified` in
`Gist.ReadbackTorsor`: the contractible form of balance dies on the
phase fragment, so balance enters as structure. `Gist` created, nine
spikes vendored from `Test` with prefixes dropped.

**The programs written for cold starts**: the initial-model program
(line 9, the coherence conjecture, the word model), the
internal-language seam (CatColab RFC 0004, five lines), the balance
dossier under line 5 with positions (C), (D), (D′). Rulings: mode
separation is not a foundation, balance goes into `virtual-graph` as
structure, strict involution not required and kept anyway. The three
staged spike prompts ran in sibling sessions and ratified the (D′)
cut (entry below).

**Close-out, `verified`**: the handedness swap adjudicated stale
(executed in the rename pass, evidence at `Type:96`, `Base:504`),
gloss T32-T34 added and T31 corrected, the future/buffer register
compression fixed at its single live site. Custody: the entry renamed
`mmmm-classical-notions` (three authors, slug as four name words),
`kiselyov-having-effect` vendored PROVISIONAL, schema admits `html`,
`resources-verify` clean at 16 entries. `inferred`, not theorems: the
(D′)-hcategory convergence and the NbE reading of readback. Open: the
(D′) profile, oracle the free balanced word model.

Commits: `7f1cf05`, `5ca957e`, `920a21f`, `1003899`, `b43fd3c`.
Session log:
[notes/2026-07-28-thunkability-balance-turn.md](notes/2026-07-28-thunkability-balance-turn.md).

## 2026-07-28 — Cat.Logic: the balance spikes, the (D′) record cut, the Bb archive

**The record cut, `verified`** (`just check-tree`: `src/Cat` 69 of
69, `src/Test` 33 of 33, `src/Bb` 16 of 16; lint clean). Position
(D′) adopted. `virtual-graph` carries `readback`, the NbE
correctness equation stated unit-free. `is-deductive-system` is
contractible cuts plus invertibility, propositional fieldwise, and
`stable` demoted from tier to theorem (`axioms→stable`). At tier
strength the four unit laws and both cancellations are theorems
(`tower.balanced`): each tier centre reads back as the other
twist, two unital magmoids on one graph, offset by the double
twist. The strict op-involution survives the field (`opⱽ-invol`
stays `refl`). The weak stratum is frozen green as
`Bb.WeakDeductiveSystem` (16 modules, new `Bb.*` namespace). Five
free-framing Gist spikes retired to it under Lane's no-red ruling,
with every `docs/` citation re-pointed. Groundwork the same day,
`verified`: the readback torsor (`Gist.ReadbackTorsor`, balance
moduli is content), the (D) rehearsal (`Gist.BalancedBase`), and
the (D′) profile gate (`Gist.BalancedProfile`, two carrier kills).

**Failed forms, recorded:** an implicit carrier over unfolding
predicates breaks on any new record field (eta recovery is
complete only while every field occurs in the hypotheses) — ruled
explicit per `docs/guidelines/elaboration.md`, which gained the
eta paragraph. Where-scoped opens of parameterized modules and
inline prop-combinator chains in copattern clauses both leave
unsolved metas; the named, module-parameter forms check.

**Open:** the (D′) associates profile, both directions. The free
balanced word model is the oracle, merged with line 9 of the
`Cat.Logic` TODO. Next step: the word-model session at (D′)
strength. Commits `0065395`, `36ef6d7`. Session log:
[`notes/2026-07-28-balanced-record-cut.md`](notes/2026-07-28-balanced-record-cut.md).

## 2026-07-14 (tenth session) — THE REFACTOR downstream committed (5 stages); a context-layer process failure surfaced, hardening opened and handed to Lane

**THE REFACTOR core downstream — five stages, all `verified` (each
reviewer-PASS + analyzer-FAITHFUL, `just check-all` exit 0):**
Stage 1 `95cc0ef` (record moved `Cat.Codep.Base`→`Cat.Type`, renamed
`hcategory`→`category`; `Cat.Coherence` retired; Gloss excluded,
byte-identical); Stage 2 `d1202b8` (`Cat.Base` redesigned — named
`emb f · g` composite relation, `cast-path⁻¹`, η-idn one-liner, the old
`emb-ext`/`emb-noy` plumbing gone); P6 `30222d6` (Iso/Covariant/Yoneda
re-pointed); Monoidal `ff481d0` (tensor alignment — a named tensor
`_·_`, full `noy/yon`→`pre/post` sweep; Spike 1 DERIVED); Groupoid
`cda12a8` (`∞-groupoid` re-assembled over the structure+axioms bundle).

**A context-layer process failure surfaced — the session's pivotal
outcome.** The `Cat.Codep` NAMESPACE RETIREMENT — Lane's standing
intention across several prior sessions — was never in the plan of
record; the planning charter (`analyzer.md:151` "the `Cat.*` canon is
`Cat.Codep`") drove the new tree to RETAIN and thread through
`Cat.Codep`. Diagnosis: the Agda-pipeline agents (analyzer/coder/
reviewer) are overfit with repo content that belongs in the knowledge
base, read as settled so it forecloses inquiry. Drafted (uncommitted): a
**single-source-of-truth law** (`.agents/CLAUDE.md`) + **methodology
P7** — content-agnostic workflow layer, agents coordinate with the
knowledge base, redundancy is a gap-probe. A methodology review found
methodology itself violates P7. **Superseded:** the plan-of-record
assumption that `Cat.Codep` is retained; `docs/roadmap.md` re-gated
(uncommitted) — `Cat.Codep` retires (a core deliverable),
Braid/Twist/Hexagon are refactor-gated not Chir.

**Handed to Lane** (session closed to Lane's direction to take control):
the methodology revision + the `.agents/` corpus audit against it.
Uncommitted, awaiting Lane: `.agents/CLAUDE.md`, `.agents/methodology.md`,
`docs/roadmap.md`. No commit after `cda12a8`; `master` is the clean
fallback. Session log:
[`notes/session-logs/2026-07-14-1729-refactor-downstream-workflow-gap.md`](notes/session-logs/2026-07-14-1729-refactor-downstream-workflow-gap.md).

## 2026-07-14 (eighth session) — process-revision backlog (F2–F5) cleared; the session-log HHMM filename convention

Object: a process/context-layer session, no mathematics. Ratified and
applied the open process-revision backlog carried from the prior
session's review, and — at Lane's direction — added and retrofitted a
timestamp grain to the session-log filename convention. Session log:
[`notes/session-logs/2026-07-14-1048-process-revisions-log-timestamps.md`](notes/session-logs/2026-07-14-1048-process-revisions-log-timestamps.md).
Uncommitted at this writing — the whole changeset (7 modified files +
12 renames + memory-file reference fixes) awaits Lane's word.

**Applied — the F2–F5 process revisions** (Lane ratified all four).
`verified` (landed to tracked homes, `just lint authoring`/`changed`
clean, each diff checked against the run ledger): F3+F6 memo-fidelity
clause (`.agents/analyzer.md:68`); F2+F5b counted-inventory
live-command convention (`.agents/CLAUDE.md:217`); F4 repo-tooling
dispatch template (`.agents/CLAUDE.md:177`, no new agent — R1
preserved); F1-siblings dual-channel sweep (`.agents/ingest.md`,
`.agents/writer.md`). F5b's *structural* self-tracking prong remains
open and deprioritized (not subsumed — flagged by the close review).

**Landed — the session-log HHMM convention** (Lane's initiative).
Filenames gain a 4-digit 24-hour time between date and slug
(`<YYYY-MM-DD>-<HHMM>-<slug>`) so same-day logs order at a glance and
sort correctly for the session-open read. `verified`: the
authoritative rule + rationale in `.agents/CLAUDE.md` "Slugs and file
naming", format strings at three mirror sites (root `CLAUDE.md`,
`.agents/CLAUDE.md:85`, `.agents/prompts/log.md` ×2), and `/log` now
derives the stamp from the close-time wall clock. 12 existing logs
renamed with `git mv` and every reference repointed — `CHANGELOG.md`,
3 intra-log cross-refs, 9 memory files — all resolve; order verified
against the logs' own content cross-reference chain.

**Process review** (`/log` close): a low-friction validation session —
encode-at-ruling-time (the primary mode), the disjoint-file-ownership
concurrency split, and deviation-surfacing all ran as designed. Two
proposals for Lane's discretion: FP2 (ratify-now, a one-clause `/log`
template fix — license omitting an empty Proposals section), FP1/FP3
(next-session questions). Report:
[`notes/research/2026-07-14-process-revisions-log-timestamps-process-review.md`](notes/research/2026-07-14-process-revisions-log-timestamps-process-review.md).

**Roadmap:** no triggers — nothing landed, was added, or was re-gated;
`docs/roadmap.md` untouched.

## 2026-07-14 (seventh session) — the bimodule spike lands (→ Cat.Bimodule); the frontmatter convention; the output-handoff fix

Object: continued the roadmap (target 1, the bimodule record spike via
`/prove`) and, at Lane's direction, adopted a library-wide frontmatter
convention and fixed a context-layer output-handoff seam. Session log:
[`notes/session-logs/2026-07-14-0949-bimodule-frontmatter-harness.md`](notes/session-logs/2026-07-14-0949-bimodule-frontmatter-harness.md).
Committed at close (this `/log`).

**Landed — the bimodule spike (roadmap target 1).** The regular
representation embeds as a bimodule hom into the internal-hom
bimodule; left-equivariance `emb (a ⨾ f) ≡ a ⟩ emb f` derives over a
full hcategory residue-free (the load-bearing ingredient is base
`interchange` via `op-comp-path` + the definitional concreteness of
the actions — NOT op's `compose-contr`), the same bridge that walls
over the abstract stratum (T23); symmetrization is thereby free over a
full hcategory. `verified`: `Test.CodepBimodule-20260713-234309`, all
checks DERIVED over β, review bracket clean (accuracy PASS-WITH-FIXES /
citations both CONFIRMED / mechanical PASS, 0 Blocking; fresh
interface-deleted re-check exit 0 zero warnings). **Lane ruled: it
promotes to a `Cat.*` library home (`Cat.Bimodule`, post-refactor),
NOT to gloss** — no ledger entry, no `Gloss.*` cert (bijection
unchanged 8↔8); the spike is the recipe until THE REFACTOR opens the
foundation (roadmap target 2 updated to carry `Cat.Bimodule`).

**Landed — the frontmatter convention** (Lane's initiative). YAML
frontmatter on tracked `.lagda.md` sources: three registers
(frontmatter metadata / a `contents:` tagline / optional synopsis
prose), required core `author`/`date`(`YYYY-MM`)/`contents`, extensible
via tolerated unknown keys. Phase-1 tooling `verified`: `site/build.py`
frontmatter rendering (byline + `contents` lede + module title; strips
before the `---`→`<hr>` rule, no leak), the `bin/lint` tolerant
frontmatter canary, and a width **soft cap at 100** (bite-tested both
directions); a limited two-file pilot (`Core.Path.Base`, `Core.Type`,
both `just check` exit 0). The styleguide Opener + Rulings rewritten.
The tree-wide bulk sweep (29 old-header files + the header-less set) is
`deferred` to roadmap target 6.

**Landed — the output-handoff reconciliation** (`HARNESS.md` +
companions). A dispatched `verifier` read the file-based-handoff
contract and the harness's "final message = result" framing as
contradictory and dropped its file-write. Fixed: HARNESS.md now states
the dual-channel rule (write the file AND return a short completion
report; the message never substitutes for the artifact), with
name-and-defer companions in `.agents/CLAUDE.md` and
`.agents/verifier.md`. `verified`: `just lint authoring`/`changed`
green. (The process review found one sibling, `researcher.md:32-33`,
carrying the mirror phrasing; Lane ratified at close and it was
reworded to the dual-channel form.)

**Process.** All bimodule checks DERIVED — no walls preserved. The
accuracy review caught loose WHY-prose (S1, corrected at four sites);
the citation review confirmed both credits (Kelly SOURCE-CHECKED,
Petrakis reworded to a see-also register). Process review: 4 friction
points, 1 ratify-now (the `researcher.md` reword), the dominant
finding a validation — eight prior-review fixes ran clean.

## 2026-07-13 (sixth session) — the ratified promotions executed; the Gloss canonization standard

Object: the queued A-batch promotions landed, and Lane's in-session
rulings hardened Gloss into a canonization tier — formal
mathematical presentation, no operational vocabulary, custody-
disciplined re-freezes — applied to all eight certificates the same
session. Everything below is UNCOMMITTED at close (one working set,
19 modified + 2 new files), awaiting Lane's commit word.

**Landed.** **T22 — the tautological filling recovers the
representable core definitionally** (verified:
`Gloss.TautologicalFilling`, frozen from the substrate spike +
`Cat.Codep.Base` @ `dde1f57`; four killchecks now run with every
check-all). **T23 — agreement ⟺ interchange-2, both routes
walled** (verified: `Gloss.InterchangeCircularity`; walls re-pinned
live, raw residues frozen). **T24 — the pentagon engine at +0**
(inferred-from-machine-check: the tracked spike @ `dde1f57`, module
A3, not frozen; the Test/ citation is Lane's granted exception,
recorded in the entry). Bijection 8↔8. **The Gloss presentation
standard** (Lane, four rulings; `src/Gloss/CLAUDE.md`): no
operational vocabulary (ledger numbers, buzzwords, contentless
labels), no templated prose, outcomes-as-mathematics with
ledger-locators-follow-the-certificate, the Test/Gloss division of
labor ("if it needs operational phrasing to be comprehensible, it
isn't ready for Gloss"), and the comment-only re-freeze custody
spec. **The retrofit of all eight certificates** under it
(verified: code tokens byte-identical to their pins under
independent comment-stripped extraction; every comment delta
enumerated; `move-r` landed in `Core.Path.Base`; `sym-∙` uses
swapped to the existing `sym-distr`; `sym-sym` verified
refl-redundant and dropped; PropPinning dead code deleted; six
operational identifiers renamed to mathematical names, rename map
awaiting Lane's veto). **The `hcategory-structure` universe
refactor** (Lane's ruling: non-inferable `h` explicit; verified:
three modules edited, downstream proven zero-edit, T10 untouched;
the earned-by-inference principle in `docs/styleguide.md` +
root-contract cross-reference; the uniformity sweep found the
library otherwise already conformant, 1 violator in 92 records).
**The hotpath CLAUDE.md audit** (Lane-invoked; scores 89/95/84/92):
nine approved edits applied — sharpest catch: the ratified
re-freeze custody spec lived only in a gitignored ledger and is now
contract-encoded; `Trait.*`/`Meta.*` rows dropped by Lane's ruling.
**`Cat.Codep.Coherent`** swapped to the Core lemmas (Lane's GO).

**Verified.** `just check-all` exit 0 at zero warnings (the
mechanical gate's independent run pre-ruling-items; the final
delta's coder run + lead spot-check per Lane's directive);
mechanical gate PASS 0-Blocking over the 17+2 tree; citation review
both Petrakis credits CONFIRMED at source; two accuracy reviews
PASS-with-fixes, all fixes applied; freeze fidelity proven by
per-block byte-match with a coverage map (now the contract's
multi-certificate reading).

**Superseded.** The pre-standard certificate presentation (run
vocabulary, T-references, templated custody boilerplate); the
one-spike-one-certificate fidelity reading; `hcategory-structure`'s
implicit hom universe; the empty `Trait.*`/`Meta.*` namespace rows.

Session log:
[`notes/session-logs/2026-07-13-2309-promotions-gloss-standard.md`](notes/session-logs/2026-07-13-2309-promotions-gloss-standard.md)
(process review inside: 7 friction points — the
ruling-vs-in-flight-lag re-proposal leads — 4 validations).

## 2026-07-13 (fourth session) — T21 independence, the Kelly lift, the shelf's machine surface

Object: the evening cascade after the shakedown close — the
extract-agree question settled by theorem, the Kelly gap closed
end-to-end, and the workflow rulings Lane made in-session landed
as they were made.

**Landed.** **T21 — extract-agree is irreducible** (verified:
`Gloss.ExtractAgreeIndependence` @ `09f7155`, frozen from the
three-arm spike @ `dde1f57`, the first tracked-Test provenance):
the equivalence class over compose-contr, the Bool/xor
countermodel killing the whole admissible candidate space, both
honest walls fenced verbatim; boundary in three clauses; three
abstract propositional strata BY THEOREM; bijection 6↔6. The full
chain ran at certificate grade — accuracy PASS, the
code-citation review's first live run (verified: caught
under-scoped Petrakis credits four upstream layers missed;
corrections applied + mirrored + a dep-arrows map addendum),
mechanical gate PASS 0-Blocking. Function-valued res-inv adopted;
the `codep-invariance` optional overlay landed (verified: green).
**The Kelly arc** (verified end-to-end): the paywalled 1964
source vendored (public re-fetch URL found by Lane, verified
byte-identical), audited 46/46 at full depth with all 21
countermodel tables at 300 dpi, the OCR mandate's first exercise
(evaluate-and-reject — the honest branch), the tracked 21-hunk
render-verified correction patch with byte-identical
regeneration, confirming pass all-PASS — **T15's ⚠️ lifts**
(audit-keyed; no ⚠️ source-identifications remain), with Kelly's
three-distinct-proof-moves correction feeding the bimodule
spike's planning. **The shelf**: full ratification (seven Vetted
lines), custody frontmatter on all eight entries with
`resources-verify` reading it mechanically, the
OCR/correction-patch custody mandates, and the
fetch-skill/ingester-split direction recorded. **The workflow
cascade** (all Lane-ruled in-session): the promotion decision
block + P3's held-promotion clause; the /log
roadmap-reconciliation stage (exercised live at this close:
target 1 LANDED, the bimodule spike now leads the roadmap);
name-keyed log Contents; the eli5 fan-out tier restored; the
verifier write-boundary scoping; uniform author/date headers;
five of six styleguide splits ruled with sweeps scheduled.

**Failed / preserved.** Arm 3's two walls — now superseded by
their own theorem (the strongest "do not re-derive"); the
`--redo-ocr` rejection record (dual-layer duplication) as the
standing reason the OCR chain evaluates rather than assumes.

**Superseded.** T15's ⚠️ and the "engine of every derivation"
reading of Kelly; the entries' body-prose hash/fetch records (the
frontmatter is the machine surface); memo A's "exactly two
strata" (three, by theorem); roadmap target 1 (landed — the
bimodule spike leads).

Session log:
[`notes/session-logs/2026-07-13-1831-independence-kelly-shelf.md`](notes/session-logs/2026-07-13-1831-independence-kelly-shelf.md)
(the held list — the three stratum ledger entries — and the
process review's eight ratify-now proposals await Lane).

## 2026-07-13 (third session) — the /prove shakedown: faithful-stratum spike + the rulings cascade

Object: the first real end-to-end `/prove` run (roadmap target 1,
the faithful-stratum substrate spike) and a cascade of workflow
rulings applied same-session. First Agda since the coherence arc.

**Landed.** The spike
`src/Test/CodepFaithful-20260713-140913.lagda.md` (verified: green,
zero warnings; independently re-checked by the accuracy review and
the mechanical gate): **A1 DERIVED** — the tautological filling
recovers `hcategory` definitionally at every operation
(function-valued res-inv; `killcheck-dot = refl`), machine-checking
the Π-integral licence; **A2 the healthy wall** —
extraction-agreement ⟺ interchange-2 pinned both ways, the
derivation from the stratum alone STUCK at the pointwise-itc2
bridge (both routes transcribed; closing would have contradicted
T13), and at the filling itc2 IS the base interchange — the 3-cell
overlay is intrinsic; **A3 DERIVED at +0** — the pentagon engine
transplants unmodified over abstract res-inv. Two memo-A
refinements pinned: function-valued res-inv (the transport-refl
trap) and the new Layer C axiom `extract-agree` (refl at the
filling; abstract strata count 3). Ledger promotion HELD for Lane.
Also landed, per Lane's rulings: Test/ tracked with two-tier
semantics and the killchecks relocated to
`src/Test/CodepCoherentKillchecks.lagda.md` (All-wired tripwire;
verified by check-all); THE REFACTOR's end state explicit in the
roadmap; Public Module Style; dated plan/research artifacts with a
self-updating path-pattern lint canary (verified: bite-tested both
directions); the `/log` process-review stage + `process-reviewer`
agent (first run delivered 10 findings; the ratify-now set ratified
and applied same-session); the code-citation pipeline
(docs/provenance.md "Code citations" owns the spec; verifier gains
the code-citation-review mode; `/prove` stage 3 gains the
conditional review); `docs/styleguide.md` distilled from a Core.*
norms survey; and `resources/bentzen-naive-cubical/` ingested at
the rijke bar and audited 57/57 CONFIRMED (verified; 0 FATAL/MAJOR
across audit + confirming re-pass), wired into `/hott` and the
contract's new Foundational references. Tooling soundness fix:
`bin/resources-verify`'s audit detection line-anchored (a prose
mention could forge load-bearing standing — found live, verified
fixed).

**Failed / preserved.** A2(4) is the expected wall, preserved
in-spike with both obstructions; salvage: the pointwise-itc2
bridge is the stratum's one missing coupling datum.

**Superseded.** The killcheck-beside-the-proof placement
(Mechanization Discipline now points at the Test/ regression
tier); the undated plan/research artifact names; memo A's
path-valued res-inv; the "verbatim"-residue wording at six
surfaces (now defined once at the contract's oracle-contract
bullet).

Session log:
[`notes/session-logs/2026-07-13-1559-prove-shakedown-faithful-stratum.md`](notes/session-logs/2026-07-13-1559-prove-shakedown-faithful-stratum.md)
(carries the pre-registered bimodule-spike design for roadmap
target 2 and the held-for-Lane rulings list).

## 2026-07-13 (second session) — pipeline reliability and the audited shelf

Object: the resources/ pipeline and the research suite, taken from
"designed" to "certified and reliability-hardened". No Agda changed.

**Landed.** The content-digest layer (statement-level digests in the
source's own terms; Rijke digested at full Part II depth by a
22-lecture fan-out) and custody mechanics (`just resources-verify`:
hashes, entry standing, consumed-by; fetch URLs and `.pdftext`
provenance recorded per entry; the chiralities extraction normalized
onto the flake-pinned poppler). The directory's doctrine encoded:
reference shelf + citation store, **information flows from resources
out, never the reverse**. Then an 8-reviewer certification — four
against the original feynman suite at `~/feynman-skills`, four
internal — certified the port **faithful** (13/13 prompt pairs, 4/4
architecture axes, zero DEFECT) and the subagent system **correctly
implemented**, and its findings were applied: the contract's new
**Layer scope** section (the source's fight-for-its-life discipline
the port had dropped, with retroactive records for `/prove` and
`/hott`), the verify protocol promoted into the contract with 15
prompts deduplicated to name-and-defer, the drifted `[unvetted]`
restatement (the review's one FATAL) deleted everywhere with a lint
canary against recurrence, skill handoffs wired, and mechanize's
audit legs closed.

**The ruling that reframed the layer (Lane):** the pipeline must be
reliable whether or not Lane reviews it. The load-bearing gate for
ingested knowledge is now the **human-free statement audit**
(identity hash-verified + digests adversarially verified against the
source, fresh-quote evidence required, records hash-bound);
ratification/veto is Lane's self-initiated discretion, never a
pipeline queue; and mathematical claims stay CONJECTURED until
machine-checked, whoever approved what. First exercise: all six
entries audited (rijke 152/155 CONFIRMED, shelf-wide 175/183), eight
corrections applied — including two dropped "locally small"
hypotheses on the mechanization target and our own memo's `†`
notation contaminating a source entry — confirming re-pass clean,
source errata recorded. `docs/gloss.md` T16 re-attributed to the
source's `(−)op` and upgraded 📐⚠️ → 📐 under the new audit-keyed
rule.

`verified`: authoring lint (with canary), resources-verify (7 hashes,
0 FATAL; all six entries audited — load-bearing capable),
unidirectional sweep, sync, shellcheck. `superseded`: the
PROVISIONAL blocking rule ("no load-bearing citation on a
PROVISIONAL entry") and the ratification queue — replaced by
audit-as-gate with discretion open. Commits `af73f50`, `e1d9f62`.
Session log:
[`notes/session-logs/2026-07-13-1323-reliability-audited-shelf.md`](notes/session-logs/2026-07-13-1323-reliability-audited-shelf.md).

## 2026-07-13 — the fresh review and the shim/prompt surface split

Object: the hardened context layer, reviewed fresh and then
restructured. No Agda changed.

**Landed.** A fresh-eyes adversarial review (an 8-reviewer workflow
with per-finding adversarial verification against rulings R1–R13)
produced 58 verified findings; all 5 FATAL, 18 MAJOR, and the
relevant MINORs were fixed — R7 Rijke propagation, R2 ingest wiring,
R6 writer dispatch, the writer↔verifier citation contradiction, the
marker-shedding-on-ratification policy, a `bin/lint` soundness fix,
and a new `just lint changed` non-regression width gate for the
in-flight tree. The flake was fixed (`poppler_utils` → `poppler-utils`
would have broken it at HEAD) and pinned with `flake.lock` (agda
2.8.0 + curl/git/gnutar/perl). Six `resources/` entries were brought
to the R11 bar by delegated `ingest` runs (`petrakis-dep-arrows`
re-ingested as LaTeX-source canonical; a `mellies-dialogue-
chiralities` duplicate removed; line-anchored maps added).

Then the **workflow surface was re-expressed as the shim/prompt
split**: full workflow bodies are masters at `.agents/prompts/`, small
auto-trigger shims at `.agents/skills/kitcat/`, Claude Code reaches
them via two directory symlinks, pi reads `.agents/` directly, and
`.pi/prompts` + `.feynman/` were removed. `.agents/CLAUDE.md` was
established as the context-layer source of truth (the repo-user /
agent-facing division of labor made explicit) and now carries the
durable R1–R13 design decisions (R10 externalization).

**Verified.** authoring lint, `just sync`, the flake devshell build
(agda 2.8.0 + all layer tools), symlink integrity, tree independence
(reworded free of the external codename, re-checked), and the 18↔18
shim/prompt pairing — all green. `verified`: those checks.
`unverified`: `just check-all` under the flake was run once during the
shakedown (green) but no Agda changed since. `blocked`: the review's
verify phase hit the monthly spend limit once (Fable 5) and was
resumed on Opus 4.8 via `resumeFromRunId` with no findings lost.

**Superseded.** The 2026-07-11 R4 ruling that "dissolved the
shim/prompt indirection" (merged skill = command) is reversed by the
split above. The old per-skill three-symlink topology (54 symlinks)
is replaced by two directory symlinks.

Three commits: `1b50416` (the amended 2026-07-12 `/log` close, with
the external codename scrubbed from history — `dev` is local-only),
`38dcb3c` (apply-pass + surface redesign), `4c7d34b` (resolved
deferrals). Session log:
[`notes/session-logs/2026-07-13-0959-fresh-review-surface-split.md`](notes/session-logs/2026-07-13-0959-fresh-review-surface-split.md).
Six `resources/` entries remain PROVISIONAL pending ratification.

**Coda (same session, post-`/log`, commit `118cd4b`).** The Rijke
foundational entry (`resources/rijke-hott/`) was given a comprehensive
part-organized section map — 3 parts, 22 lectures, 247 line anchors at
`<lecture>.tex:LINE` (extracted per-lecture by a 22-agent workflow,
spot-checked against the source). A new `/hott` skill (the 19th) does
reference lookups grounded in that map: the standard formulation
SOURCE-CHECKED at the line, plus the kitcat cross-reference. Adding it
needed only the two masters — the directory symlinks surfaced it in
both harnesses — the first exercise of the new surface design.

## 2026-07-12 — the context-layer hardening arc

The feynman-derived context layer was audited against a studied
reference implementation of the same workflow discipline (like-with-
like, benched on this repo's own mathematics work) and hardened into
the library's own. Landed: `.agents/methodology.md` (the five working
principles stated as kitcat's own, with kitcat exemplars); the
bind-once cross-agent contract `.agents/CLAUDE.md` with the 18 skills
slimmed to defer to it; the roster restructured (`analyzer` = merged
theoretician + structural analyst; `coder`/`reviewer` renamed; new
`ingest`/`writer`/`suite-maintainer`); every working protocol
(spike/killcheck-refl/STUCK-wall/graduation) encoded from root
CLAUDE.md through the agents; a repo-owned `flake.nix` pinning the
latest stable Agda + ingestion tools; `just sync` gating on drift and
a new `just lint authoring` gate; the `/prove` pipeline command;
`resources/` given a canonical-source-format + `.pdftext` cache
convention; and the Rijke foundational entry (arXiv 2212.11082) as
the first live ingestion. The layer was corrected to full public
independence (no external-repo references; the methodology stands on
kitcat's own exemplars). notes/plans + notes/research became local
working memory. `verified`: authoring lint, spike-echo, symlink
integrity, tree independence, flake syntax. `unverified`: `just
check-all` under the flake (no Agda changed; last green `593f44a`).
`blocked`: five `resources/` entries + Rijke are PROVISIONAL pending
ratification. Superseded: the reboot's harness-mechanics claims
(re-audited against live builds) and the ad-hoc convention set.
Commits `f70cf94`, `6103b7f`, `202dfe7`, `9e4dfaf`. Session log:
[`notes/session-logs/2026-07-12-0313-context-layer-hardening.md`](notes/session-logs/2026-07-12-0313-context-layer-hardening.md).

## 2026-07-11 — the context-layer reboot (feynman port)

The repository's context management layer was rebooted: the
feynman.is research workflows were ported into a kitcat-owned,
harness-generic suite (`.agents/skills/kitcat/` — sixteen workflows
+ the HARNESS.md capability rosetta + the `spike-echo` diagnostic),
morally translated from ML research to mathematics research, and
**verified live on both harnesses** (Claude Code via `.claude/skills/`
symlinks; Pi natively plus typed `/name` adapters in `.pi/prompts/`
and `.feynman/prompts/`) — all from one canonical file per workflow.
Landed alongside: `docs/provenance.md` (binding honesty standards:
strict VERIFIED/SOURCE-CHECKED/CONJECTURED/`[unvetted]` labels, nine
practices, AI-contribution statement, date-stamped policy context);
the `resources/` vetted-sources convention (hash-verified vendored
documents, gitignored, records tracked); `docs/roadmap.md`;
CLAUDE.md rewritten as the cross-harness contract (root AGENTS.md
deleted — Pi prefers it over CLAUDE.md, verified in source); README
adapted (identity, provenance section, build; dead credits fixed).
The agent roster shipped with it: six definitions in `.agents/`
(`researcher` and `verifier` ported from the feynman originals;
four Agda specialists written fresh from the contract), registered
across all three harnesses by symlink — discovery verified live.
A six-lens whole-suite review (Opus) ran before staging; its 2
FATAL and 6 MAJOR findings are fixed (verified: the fixes are in
the staged tree). A nine-unit adversarial porcelain sweep then cut
the tooling that had no established place — `log-failure`/`Log/`,
the `deps` cluster, `benchmark`, `html-deploy`, `check-dirty`,
lint's imports check — fixed `mmv`'s unsafe rename sweep, and kept
the verified core (`check`/`check-all`, `sync`, `lint`
width+flags, `new`, `html`/`html-serve`, `stats`/`wip`);
`src/Test/` and `Stash/` are now gitignored scratch (Gloss the
upgrade path), and `All.lagda.md` no longer imports untracked
scratch (clean clones typecheck again — verified). Branch renamed
to `dev`.
**Superseded and retired to `.attic/`**: the pre-reboot context
layer — design.md, architecture.md, lexicon.md, styleguide.md,
coh.md, handoff.md (replaced by this file + the session-log chain +
the roadmap), six pre-reboot research memos, the four agent
definitions, and the docs-drift porcelain (recipe removed).
No Agda changed; `just check-all` not run (last green `593f44a`);
everything staged, commit pending Lane's go-ahead. Session log:
[`notes/session-logs/2026-07-11-1809-context-layer-reboot.md`](notes/session-logs/2026-07-11-1809-context-layer-reboot.md).

---

## 2026-07-11 — Cat.Codep: the coherence tower, closed by theorem

*Retroactively reconstructed 2026-07-12 (the mathematics work of the
day; the reboot above is the same day's later infrastructure
session).* The coherence overlay landed: `Cat.Codep.Coherent`
(θ-core derived, the gauge cluster collapsing to no fourth cell —
T6/T7/T19) and the Mac Lane `Triangle` (weak/full/mirror — T8), with
the parity theorem's Route-B upgrade on `Op` (T9). The theorem
ledger `docs/gloss.md` (T1–T20) and five frozen `Gloss.*`
certificates (EightFieldWall, PathGroupoid, PcomConservation,
PropPinning, TriangleFace23 — all `@ 9133396`) were committed
together in exact ledger↔certificate bijection. TEL-independence
(T11, S² countermodel + EightFieldWall), the op-involution regress
(T12), and the prop-pinning trichotomy (T13) established; the
interchange / Kelly / Melliès / binary-ancestor identifications
(T14–T17) recorded 📐. `verified` (`check-all` exit 0). This
session's commits `cfccb0b`, `9133396`, `2327309`, `593f44a`.
Session log:
[`notes/session-logs/2026-07-11-1200-codep-coherence-tower.md`](notes/session-logs/2026-07-11-1200-codep-coherence-tower.md).

## 2026-07-10 — Cat.Codep: hcategory reshape + the opposite category

*Retroactively reconstructed 2026-07-12.* The representable core was
reshaped to the flat-carrier `hcategory` record (collapsed tower),
and the opposite category `Cat.Codep.Op` landed with the parity
theorem — pre/post definitionally swapped, every mirror axiom
derivable (T9), giving strict self-duality of the category core
(T10); the eval axiom is self-mirror, so bias is chirality (T3). The
`Gloss.PcomConservation` (T20) and `PathGroupoid` (T18) spikes were
produced here (certificates frozen the next day, `2327309`).
`verified` (per-commit machine-checked). Commits `40e6743`,
`ed94308`, `97e3157`. Session log:
[`notes/session-logs/2026-07-10-1200-hcategory-reshape-opposite-category.md`](notes/session-logs/2026-07-10-1200-hcategory-reshape-opposite-category.md).

## 2026-07-09 — Cat.Codep: the representable trilayer

*Retroactively reconstructed 2026-07-12 (the overnight session; git-
local dates place it on the 9th).* The `Cat.Type`-style category was
rebuilt as `Cat.Codep`: a category presented through a representable
embedding `emb : hom ↪ composite`, the 4-field
representability-canonical carrier, and the `structure` / `axioms` /
`category` trilayer split (defeating a walking-arrow termination
class). Ancestors of ledger T1 (`Cat.Codep.Base`) and T4
(`Cat.Codep.Coherence`); the conservativity battery's path-groupoid
witness is the T18 ancestor. `verified` (five commits
machine-checked). Commits `dc52571`, `2376d5b`, `bd75cd1`,
`b5756c1`, `9bddaf8`. Session log:
[`notes/session-logs/2026-07-09-1200-codep-representable-trilayer.md`](notes/session-logs/2026-07-09-1200-codep-representable-trilayer.md).
