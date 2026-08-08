# Changelog — Bb.VirtualGraphs

Every alteration and addition to this tree after it entered the
archive. **Newest entry first.** The tree is frozen green, so an
entry names the checker run that says so.

---

## 2026-08-08 — the diagonal, and one statement per statement

**Twenty-one modules in `Degenerate`, eleven in the mainline,
`verified`.** The criterion widened to cover any degenerating
construction, which admits a fourth hypothesis: setting the two
half-twist families equal. Five modules read a single family filling
both argument slots and so moved. `Engine` became
`Degenerate.Chosen`, `Lens` merged into `Degenerate.Lens`, and
`Stable`, `Displaced`, and `Curried` moved whole. Five `Degenerate`
modules that already sat downstream of the chosen-edge vocabulary
stopped reaching across the namespace boundary to find it.

`Chosen`'s vocabulary is now the framing at the diagonal rather than
a second copy of it. `var`, `covar`, `eval`, `act`, `coact`, `act-π`,
and `coact-π` come from `framing G idn idn`. The two composites come
from `framing⁻`/`framing⁺` with the signs crossed, which is where the
crossing between the two `⁻`/`⁺` registers is now stated, once.
`dict` keeps `graph` and the two hands and drops ten dictionary
entries proved by `refl`, none of which had a user in this tree.
`Lens`'s injections come from the framing the same way, and its
two-sided base, `bipush`, and judgment family from `Graph.two-sided`.

Readback had four names for one type. `framing.readback-of` is the
survivor. `lens.readback` went, `Stable.readback` and
`Degenerate.Reflexive.readback` and `Degenerate.Engine`'s
`stability.readback` now read through it, and `candidate.rb` is
defined by it.

`Embedding` gained the swap of arguments: `swap-arg`, its inverse,
`swap-judgment` with its inverse and equivalence, `ap-swap`, and
`rep-op`. These read no half-twist and carried a vestigial `idn`
parameter they never used. They had been stated once in `Engine` and
again in `Stable`. `Engine`'s involution block went with them, its
three remaining lemmas being `refl` with no user.

`Naturality` is new, cut from `Tower`'s last section. `Framing` keeps
the two tiers, which read the framing alone. The transfer between the
tier form, the judgment form, and the flank equation needs the tower,
so it could not live beside the statements it transfers. `Tower` fell
from 319 code lines to 221, which puts every theory module inside the
300-line budget.

`Degenerate.Absorb` gained `from-cancel`. The passage from a
cancellation to the absorption of a whole argument half had been
written out five times, four of them with an identical proof term, in
`Cancellation`, `Display`, `Neutral`, `Extraction`, and
`Degenerate.Tower`. It takes the family as a parameter, since
`Extraction` absorbs at a tier's projected centre rather than at a
half-twist.

`Recognition`'s `law₀` and `law₁` are `Mediation`'s `clause₀` and
`clause₁` read at the candidate pair the framing supplies, and are now
defined that way. The two modules stayed separate: each has a model
counterpart under `Word`, `Circle`, or both, and merging the theory
pair would leave those four models named for modules that no longer
exist.

`Degenerate.UnitShape` no longer imports `Groupoid.Path`. Its
`self-path` module was a path-groupoid computation, and it moved into
that model as `unit-clause⁺`/`unit-clause⁻`, renamed off `collapse⁺`
and `collapse⁻`, which `Tower` already uses for different lemmas.
`Degenerate.Interchange`'s crossed unit laws became `unitl⁺-rx` and
`unitr⁻-corx`; `unitl⁺` named one statement there and a different one
in `Cancellation`.

`just check-tree src/Bb/VirtualGraphs`: 55 of 55. `just check
Bb.index`: green.

---

## 2026-08-08 — the `Degenerate` namespace

**Seventeen modules in a new namespace, `verified`.** A
module belongs in `Degenerate` when its telescope supplies a unit, an
absorption tier, or a readback of the half-twists, or when it derives
one of those from something weaker. Each of those hypotheses makes the
twist act as the identity, which collapses the two hands to a single
composition. The tree states the general case, so the cases that admit
the collapse are segregated rather than left beside it.

Moved whole: `Cancellation`, `CrossedUnit`, `Diagonal`, `Display`,
`Extraction`, `Gluing`, `Interchange`, `Neutral`, `Presentation`,
`Readback`, `Reflexive`, `Shape`, `UnitShape`. `CrossedUnit` and
`UnitShape` qualify entire. Every declaration in `CrossedUnit` sits
inside a submodule taking the tier, and in `UnitShape` the datum is
the absorption equation itself, `self` states the tier in
self-standing form, and `self-path` reads it at the path groupoid.

`Interchange` moved whole rather than split. Its only non-degenerate
declaration was `cuts-agree`, the predicate that the two hands agree,
which is the collapse condition `Diagonal` already names as such.

`Degenerate.Absorb` is new. It holds `is-absorbing⁻`/`is-absorbing⁺`
with their propositionality, extracted from `framing⁻`/`framing⁺`;
`op-absorbing⁻`/`op-absorbing⁺`, extracted from `Framing`'s `duality`;
the same tier anchored at a candidate framing with its two fiber-point
lemmas and `self-read`, extracted from `Recognition`'s `candidate`;
and `absorb`/`obstruction`, extracted from `UnitShape`.
`framing.readback-of` stays in `Framing`. It describes a general
predicate, so the type name is not itself a degeneracy. Terms of it at
the half-twists are, which is why `self-read` crossed over.

`Tower`, `Lens`, and `Engine` split. `Degenerate.Tower` takes
`Tower`'s last hundred lines: `absorption`, which takes the twist
cells pinned to the second projection and returns both absorptions,
and `unital`, which returns one near unit law per hand from them.
`Degenerate.Lens` takes everything from `unital` onward, about three
quarters of the file; the axiom-free vocabulary stays. `Lens`'s
leading module was anonymous and is now named `lens`, so the
extracted half can open it. `Degenerate.Engine` takes `engine` and
everything under it, and the two unital hands of the dictionary.

`Engine`'s `hand⁺` changed shape rather than only moving. It bundled
`contr⁺` and `absorb⁺` in one telescope, while `hand⁻` separated them
into `hand⁻ (contr⁻)` and a nested `unital (absorb⁻)`. Extracting
`hand⁺` whole would have carried the positive hand's composition out
of the mainline while the negative's stayed, so `hand⁺` now mirrors
`hand⁻`, and `reflect-⨾` for the positive hand is new. Nothing
depended on either.

`Shape`'s `is-deductive-system` and `Gluing`'s
`is-coherent-deductive-system` are now
`is-deductive-system-depreciated` and
`is-coherent-deductive-system-depreciated`. Both define recognition
with the two absorption fibers as conjuncts, so a recognized pair
makes the twist trivial, and neither definition earns the shorter
name. The unrelated records of that name in `Bb.WeakDeductiveSystem`
and `Cat.Logic` are untouched.

Fourteen theory modules stay beside `Type`, and no mainline module
imports `Degenerate`. Every mainline file is clean at the module
level, not only at the import level. `Pentagon` takes a half-twist family, the
embedding condition, and one composability hypothesis per hand, and
nothing else. `Twist` holds naturality and neutrality, which are
statements about slot occupancy and collapse nothing.

`Displaced` reaches `Lens`'s `inj⁻`/`inj⁺` through `open lens` now.
The `outputs/virtual-graphs-surface-*` reports were repointed at the
new paths.

`just check-tree src/Bb`: 153 of 153 modules typecheck.
`just lint changed`: clean.

## 2026-08-07 — `Twist`, the ternary-layer twist

**One new module, `verified`.** The twist at the primitive ternary
layer, over the two half-twist families `rx` and `corx`. The carrier
holds no field beyond reflection. Two of the three slots of one
reflection hold one half-twist each, one of each sign, so their
junction, the twist, acts on the third without ever being named as
an edge. Landed:

- `θ-left`/`θ-right`, the two actions, read off `Framing`'s `cell⁺`
  and `cell⁻`. Each cell already carries one half-twist of each sign,
  so each is the twist acting on a single edge. The left action holds
  the edge in the coterm flank, the right in the term flank.
- `θ-nat`, the naturality predicate, with its mirror `θ-nat'` and the
  two conversions. It reads `rx ⨾ corx ⨾ f ≡ f ⨾ rx ⨾ corx`, so the
  twist is central, and the mirror is the pointwise symmetry.
- `θ-neutral` asking each action to be an equivalence, and
  `θ-neutral-is-prop`. Neutrality is property and not structure.
- `θ-halves`, `θ-nat→neutral-left`/`θ-nat→neutral-right`, and
  `θ-nat→neutral`. Under naturality the two actions are one map, so a
  single component delivers the pair.
- `θ-left≃`/`θ-right≃`, `corx-inv`/`rx-inv` with their counits. An
  action carries one half-twist of each sign, so the preimage of one
  family cancels that family and leaves the inverse of the other. The
  two hands cross, matching `Framing`'s crossing of the framing and
  composition registers.

`θnat` is spelled `θ-nat` here, matching the tree's kebab-case
convention inside modules. `θ` names the twist alone. The extracted
preimages carry the half-twist names, so `θ` never stands for a half
of anything.

The model modules and the readback clause ladder from the same spike
line stay in `Test/` for now.

`gtimeout 300 just check Bb.VirtualGraphs.Twist`: exit 0.
`just check-tree src/Bb`: 149 of 149 modules typecheck.
`just lint changed`: clean.

## 2026-08-06 — `twist` renamed to `half-twist`, tree-wide

**Naming only, no statement changed, `verified`.** Every `twist` in
this tree now reads `half-twist`. A carrier posits one family, and
that family is a half-twist. The full twist is its double, which no
carrier holds as an edge. The old word named the wrong grade, and it
covered both grades at once, so it hid a distinction the theory
depends on.

The sweep covers identifiers, prose, and the tree's records
(`README.md`, `HISTORY.md`, `TODO.md`, and this file). It is
retroactive. Earlier entries now use the corrected term, so no
reader meets the old grade claim anywhere in the tree. Compounds
keep their reading. `double half-twist` names the full twist, and
`half-twist⁻`/`half-twist⁺` name the polarity pair.

The sweep stops at this tree. `Bb.OneTwist`,
`Bb.CatsWithExplicitInterchange`, and `Bb.WeakDeductiveSystem` keep
`twist` in their own identifiers and prose.

`gtimeout 2400 just check Bb.index`: `verified`, 148 modules.
`just lint changed`: clean.

## 2026-08-06 — HISTORY citation re-pointed after the plan set was cut

**Documentation only, no module changed.** The composite-rx refactor
narrowed to `Core.Kan`, `Core.Composite`, and `Core.Rx`, and its
per-stage documents merged into
`docs/composite-rx-refactor/stages.md`. `HISTORY.md`'s 2026-07-24
entry quoted `architecture.md`, which no longer exists. The entry now
states the same naming ruling against the plan directory, without the
verbatim quotation, since no file carries that wording now. The
ruling, the attribution, and the commit reference are unchanged.

No `.lagda.md` file changed, so the tree's green state is unaffected.

## 2026-08-06 — `JudgmentLens`/`TwoSided`

**Two new modules, `verified`.** Vendors the last two
`Bb.NaiveVirtualGraph.Gist` rows, held out of phase 3 for carrying a
second record: `Lens.lagda.md` and `Displaced.lagda.md`. Plan:
`outputs/.plans/virtual-graphs-vendor-phase4.md`.

`Lens.lagda.md` packages the chosen edge's judgment and hom families
as lenses instead of fibrations. It imports `Engine` for `chosen`,
`composable`, and `dict` rather than re-deriving that vocabulary. It
re-derives `unit⁻-is-idn`/`unit⁺-is-idn`/`idn-absorb⁻`/`idn-absorb⁺`
locally, though. `Engine`'s own copies sit three module-parameters
deep, behind `contr⁻`/`contr⁺` this file's `module unital` has no
use for. Landed:

- `inj⁻`/`inj⁺`, and `judgment-lens : unbiased-lens graph judgment±`
  with its univalent display.
- The flank-coherence scoping remark: `munitor-at-rx`,
  `flank⁻-of`/`flank⁺-of`, `flanks-agree`.
- The two-sided base's own lens, `two-sided-lens : oplax-cov-lens
  two-sided judgment-fam`, and the cospan suite:
  `push-is-composite⁻`/`⁺`, `interchange-is-cospan`,
  `cospan-is-interchange`.
- `hom-lens : unbiased-lens graph hom±`, `bipush-comp`, and
  `interchange→composites-agree`.

`TwoSided`'s bare `mediation` renames to `composites-agree`, matching
`Engine`'s `units-agree`. `Bb.VirtualGraphs.Mediation` already owns
`mediation` for a different, richer notion. Both source files
independently named their lens `judgment-lens`. Landed side by side,
the two-sided one is `two-sided-lens`.

`Displaced.lagda.md` holds the displayed carrier `virtual-graphᴰ`
and its Σ-by-Σ vocabulary (`term[_]`, `coterm[_]`, `argument[_]`,
`conclusion[_]`, `judgment[_]`, `var[_]`, `covar[_]`, `act-π[_]`,
`coact-π[_]`, `inj⁻[_]`, `inj⁺[_]`). Not carrier-generic as first
scoped: `idn[_]`'s own type names the base `idn` directly, so the
file takes the same `(idn : ...)` parameter and `Engine` import as
`Lens.lagda.md`.

`Bb/index.lagda.md` gained two import lines (`Displaced`, `Lens`),
alphabetized into the existing block.

**State, `verified`.** `just check-tree src/Bb`: 148 of 148 modules
typecheck. `just check Bb.index`: clean. No postulates, no unsafe
markers, no `-W` suppression.

Next: the `Bb.NaiveVirtualGraph.Gist.PathGroupoid` model is the one
row left unvendored. The three literature-vendoring items and the
README prose-debt item `TODO.md` still lists.
`Bb.OneTwist`/`Bb.VgCategoryShape` retirement, pending Lane's
go-ahead (`src/Bb/TODO.md`).

## 2026-08-06 — the remaining `Bb.NaiveVirtualGraph` chosen-edge rows

**Five new modules, two extended, `verified`.** Vendors the seven
items `outputs/.plans/virtual-graphs-vendor.md` named as deferred
beyond `UnitShape`:

- `UnitCanonical`'s canonical suite and half-adjoint obstruction
- `CrossedUnit`
- `AbsorbObstruction`
- `DeductiveSystem`'s route-naturality suite
- `StableFiber`'s packagings and op-transport
- `ReflexiveVG`
- `PerHandUnit`'s curried forms

`JudgmentLens`/`TwoSided` stay unvendored: a displayed carrier, a
second record, outside the tree's one-record rule. The
`Bb.NaiveVirtualGraph.Gist.PathGroupoid` model is also not in this
pass. Plan: `outputs/.plans/virtual-graphs-vendor-phase3.md`.

`Engine.lagda.md` gained a "## Stability" section: the third tier off
one bare `readback` hypothesis, `eval-is-coact`/`eval-is-act`, and
the readback-alone canonicity route. It also gained the
route-naturality suite (`route⁻`/`route⁺` and their naturality,
`unique-agrees⁻`/`⁺`) and the half-adjoint obstruction
(`half-adjoint-forces-truncation`). `UnitShape.lagda.md` gained
`module absorb`/`module obstruction`: a propositional predicate that
delivers absorption forces every self-path of the chosen family to
die under `ap held`, unconditionally. The flat-telescope carrier let
the source's record-perturbation step drop out entirely, since `idn`
was already the sole free variable.

Three new theory files. `CrossedUnit.lagda.md`: the coterm hand's
derived filler feeds the term hand's tier one field early. Once an
exchange hypothesis is supplied, the chosen family is that tier's
unique inhabitant. `Reflexive.lagda.md`: the chosen edge with its own
two absorptions as hypotheses rather than derived facts. It is
canonical for free given a unit-fiber hypothesis, and (`redundancy`)
the unit tier drops entirely once stability is stated as an
equivalence. `Stable.lagda.md`: the equivalence-plus-idempotence
route to absorption, three stability formulations side by side, and
the full op-transport suite across the opposite carrier.

One new file with a self-contained local carrier. `Curried.lagda.md`
restates the two-hand theory over a ternary `emb` operator and two
compositions as fibers over strings. Readback is one statement rather
than two, and the flank agreement between the two hands is
well-formed but supplied by neither hand's own data.

One new model file. `Groupoid/Engine.lagda.md` gives the discrete
path-groupoid witness for all five theory modules above: every
hypothesis telescope holds untruncated, with no h-level condition on
the carrier.

`Bb/index.lagda.md` gained five import lines
(`CrossedUnit`, `Curried`, `Reflexive`, `Stable`, `Groupoid.Engine`),
alphabetized into the existing block.

**State, `verified`.** `just check-tree src/Bb/VirtualGraphs`: 48 of
48 modules typecheck. `just check Bb.index`: clean. No postulates, no
unsafe markers, no `-W` suppression.

Next: the `Bb.NaiveVirtualGraph.Gist.PathGroupoid` model, not named
in this pass. The three literature-vendoring items and the README
prose-debt item `TODO.md` still lists. `Bb.OneTwist`/
`Bb.VgCategoryShape` retirement, pending Lane's go-ahead
(`src/Bb/TODO.md`).

## 2026-08-06 — five lemmas promoted to Core and HData

**Two files, `verified`.** Lane approved every item in
`outputs/virtual-graphs-core-proposals.md`. `snd-contr` moved to
`Core.Transport.Properties`, beside `is-contr-×` (its converse), with
a new companion `fst-contr`. `diagonal` and `loops→is-set` moved to
`Core.HLevel.Base`. `equiv-cancel-l`/`equiv-cancel-r` moved to
`Core.Equiv.Properties`, renamed `equiv-lc`/`equiv-rc` (`t ∘ s` writes
`t` on the left and `s` on the right; `equiv-lc` cancels the left
factor, `equiv-rc` the right). `mult-r-equiv` moved to
`HData.Circle.Mult`, beside `mult-equiv`. `ap-mult-base` and
`slide-rot` moved to `HData.Circle.Properties`, which already carried
a private copy of `ap-mult-base` for its own use, now made public.
`Circle.Recognition` no longer imports `Circle.Mediation` — that
import existed only for `mult-r-equiv`.

**Two renames and a relocation, `verified`.** `wind` was asked for
"the Path module (where invl/cancell live)" — that is `Core.Kan`'s
`module Path`, not `Core.Path.Base` (a different file, holding
higher-level lemmas built on `Path`'s primitives). `Core.Path.Base`'s
`cancell` is confirmed left-cancellation (it cancels the `sym p ∙ p`
pair on the left of a composite) and `cancelr` right-cancellation
(the symmetric pair). All three — `wind`, `cancell` renamed `lc`,
`cancelr` renamed `rc` — moved into `Core.Kan.Path`, reached as
`Path.wind`/`Path.lc`/`Path.rc` everywhere, matching the tree's
existing `Path.invl`/`Path.assoc`/`Path.commutes` convention. Swept
across every live caller: `Core.Path.Base` itself (`move-r` and
`conj-cancel`, its remaining residents), `Core.Path.Exchange`,
`Cat.Logic.Gist.ReadbackShift`, `HData.Circle.Properties`, and four
`Bb.VirtualGraphs` files (`Embedding`, `Circle.Natural`,
`Circle.Recognition`, `Circle.Shift`). Two more files
(`Bb.WeakDeductiveSystem.Gist.FramedCut`, `Bb.VirtualGraphs.
Groupoid.Path`) each carry an unrelated local `lc` of their own
(reflection injectivity, not path cancellation) that briefly collided
with an intermediate unqualified form of this rename; both are back
to their original, unqualified `open import Core.Path.Base`, since
`Path.lc` being qualified-only removes the collision without any
`hiding` clause. Ten `src/Test/Spike*.lagda.md` files still call the
old names; `Test.*` is gate-exempt and those files are out of scope.

**One duplication resolved, `verified`.** `cross⁻`/`cross⁺`/
`cut⁻-cross`/`cut⁺-cross` now live once, in bare `Tower.tower` at
group C (taking the missing near unit law as an explicit argument,
since group C has no absorption hypothesis to supply it
unconditionally). `Cancellation.collapse` and `Neutral.neutral` both
instantiate from there now instead of restating. `Circle/Natural.
turn`'s local copy is deleted, inherited transitively through
`naturality`/`tower`. Three sites carried this duplication in total.
Landing the promotion broke two of them with `ClashingDefinition`:
`Cancellation.collapse` (found and fixed first) and `Neutral.
neutral` (found only once the promotion had already landed, not on
any original list). Both took the same fix: a qualified
`tw = tower ...` alias, `hiding` the two clashing names on the
transitive open, and a one-line reinstantiation against the module's
own already-derived unit law.

**State, `verified`.** `gtimeout 590 just check-tree` (whole
repository, 389 modules): 373 typecheck. The 16 that do not are
`Core/Coherence/Paths.lagda.md` and `Core/Path/Coherence.lagda.md`
(pre-existing, a stale import predating this session), the four
`Data/Thin/*` modules (pre-existing, tracked separately), and ten
`src/Test/Spike*.lagda.md` files (gate-exempt). Zero postulates, zero
`TERMINATING`, zero unsafe features, across every touched file.

---

## 2026-08-05 — the recognition line, vendored

**Thirteen new modules, six extended, `verified`.** The
`TODO.md` item covering the thirteen 2026-08-02/03 `Test.Spike*`
files (hypothesis groups E and F) is closed. Plan:
`outputs/.plans/virtual-graphs-vendor-phase2.md`. Every module
restates checker-verified lemmas only, over this tree's carrier and
its already-landed hypothesis-group telescopes; no spike's own
reading of what a result meant for the recognition line crossed
over, including the five circle-model verdicts
`notes/2026-08-03-vgds-torsor-correction.md` had already flagged as
contaminated interpretation over sound proofs.

New: `Recognition`, `Shape`, `Gluing` (the candidate-relative kit,
per-object shape, and cross-pair grammar, from
`SpikeCandidateGenerator`, `SpikeGradeSelector`, `SpikeFramedShape`,
`SpikeGluingCharacteristic`, `SpikeEdgeCoherence`). `Neutral` (group
E, from `SpikeNeutralTier`, the second route to the polarity
collapse `Cancellation.collapse` also reaches). `Mediation` (the
mediation clauses and Kraus canonicalization, from
`SpikeMediationWild`, `SpikeSelfMediation`, `SpikeTwistMediation`).
`Bool.Endo` (the commuting-involution models, from
`SpikeNeutralReadback`). `Bool.Sleeve` (the sleeve carrier, from
`SpikeEdgeCoherence`, `SpikeGluingCharacteristic`). `Word.Mediation`,
`Word.Census`, `Word.Recognition` (the word-model instances of the
above six spikes plus `SpikeCandidateGenerator`, `SpikeGradeSelector`,
`SpikeFramedShape`). `Circle.Natural`, `Circle.Mediation`,
`Circle.Recognition` (the circle-model instances, from
`SpikeNaturalTier`, `SpikeNaturalTruncation`, `SpikeNaturalModuli`,
`SpikeMediationWild`, `SpikeSelfMediation`, `SpikeCandidateGenerator`,
`SpikeFramedShape`, `SpikeGluingCharacteristic`; `--cubical`, joining
the tree's existing circle island).

Extended: `Framing` (the six half-twist-pairings and naturality tiers,
from `SpikeNaturalTier`, `SpikeNaturalTruncation`). `Tower` (the four
flanking operations and their law types, the naturality-tier
machinery, from `SpikeNeutralReadback`, `SpikeNaturalTier`,
`SpikeNaturalTruncation`). `Embedding` (the centred pair and
`path-lc`, from `SpikeNaturalTier`, `SpikeNaturalTruncation`).
`Readback` (the naturality-far-law equivalence, from
`SpikeNaturalModuli`). `Bool.Readers` (the four-reader model's
failing negative naturality square, from `SpikeNaturalTier`).
`Groupoid.Path` (both naturality tiers at an arbitrary self-path
family, from `SpikeNaturalTier`).

A handful of cited rows dissolved on restatement rather than
landing: `SpikeNeutralReadback`'s restated tiers and tower duplicate
already-landed `Framing`/`Tower` content; `SpikeFramedShape.reframe`
has no work to do over this tree's already-parameterized
architecture; the four `derived` closures in `Shape.recognized` are
`Tower.tower`'s own closures, inherited rather than restated.

Two housekeeping items follow from the landing, both noted in
`TODO.md`. `cross⁻`/`cross⁺` and their crossed-cut laws are now
stated in two places, `Cancellation.collapse` and locally inside
`Circle/Natural.turn`. Bare `Tower` still lacks them at group C, with
no absorption hypothesis, which is where they belong. Separately,
`Circle.Recognition` imports `Circle.Mediation` for one lemma
(`mult-r-equiv`) that `outputs/virtual-graphs-core-proposals.md`
proposes moving to `HData.Circle.Mult`.

**Core-placement proposal, `verified`.**
`outputs/virtual-graphs-core-proposals.md` names five carrier-free
lemmas found during the vendoring (`snd-contr`, the `diagonal`
module and `loops→is-set`, `equiv-cancel-l`/`equiv-cancel-r`,
`wind`, `mult-r-equiv`) with their exact statement, a searched
`Core.*`/`HData.*` home, and what that search found. Nothing has
been moved; the proposal is for review.

**State, `verified`.** `gtimeout 590 just check-tree
src/Bb/VirtualGraphs`: 43 of 43 modules typecheck. `just check
Bb.index`: exit 0, after thirteen new import lines. `just lint
changed`: all checks passed. Zero postulates, zero `TERMINATING`,
zero unsafe markers, grep-confirmed across every new and extended
file.

---

## 2026-08-05 — HISTORY.md, the tree's narrative record

**One file, `verified`.** The tree's one permitted exception to the
archive's no-narrative rule (`src/Bb/CLAUDE.md`). Six hundred and
thirty-six lines, fifteen dated sections from the mid-July 2026
monoidal-coherence precursor through the naming audit and the
negative pentagon, each beat cross-referenced to its current module.
Sources: `notes/*.md` 2026-07-14 through 2026-08-04, `src/Cat/Logic`'s
`TODO.md`/`gloss.md`/`lemmata.md`, the deleted `docs/deductive-systems/`
(recovered via `git show 8f4be13^:`), `docs/composite-rx-refactor/`,
and every other `Bb` tree's own `README.md`/`CHANGELOG.md`.

**State, `verified`.** Every identifier, module reference, and quoted
ruling cited as living "here now" grep-checked against its claimed
location and confirmed. The `writing` skill's self-lint:
0.70 violations/100 words, exit 0.

---

## 2026-08-05 — stability, as prose, follows the identifier

**Sixteen files, `verified`.** The naming pass two entries below
renamed the identifier (`is-stable` → `reflect-is-embedding`,
`Stability` → `Embedding`); this entry catches up the prose that
still said "stability"/"stable" as an informal description of the
same condition. `Cancellation`, `Display`, `Engine`, `Diagonal`,
`Embedding`, `Framing`, `Interchange`, `Pentagon`, `Readback`,
`Tower`, `Bool.Readers`, `Bool.Klein`, `Circle.Model`,
`Circle.Polarity`, `Circle.Thunkable`, `Circle.Shift`, and
`Group.Abelian` are reworded: "stability" becomes "the embedding
condition," "stable" as an adjective becomes a plain statement that
reflection is (or yields) an embedding, per sentence. Local
bindings named `stable` (a witness of `reflect-is-embedding` at a
model, e.g. `Diagonal.pinned.stable`, `Circle.Model.circle.stable`,
`Group.Abelian.framed.stable`) are untouched — informal local
names, not the audited identifier. Generic "half-twist" as an ordinary
descriptive word is untouched throughout the tree: unlike
"stability," it does not import a specific established concept the
corpus fails to earn, so purging it was not warranted by the same
reasoning.

**State, `verified`.** `gtimeout 280 just check-tree
src/Bb/VirtualGraphs`: 30 of 30 modules typecheck. `just lint
changed`: all checks passed.

---

## 2026-08-05 — the negative pentagon, through the opposite

**Three modules, `verified`.** The pentagon now holds for both
hands. The negative one is the positive theorem read at `opⱽ G`,
not a second path argument.

`Embedding.lagda.md` gains `reflect-lc-fiber`. Two representations
`u v` of one judgment name a path of edges twice — cancel
`reflect` across `u .snd ∙ sym (v .snd)`, or project the fiber's
own `S α u v` — and the lemma identifies the two. `tower⁺` and
`tower⁻` build their associators along those two routes
respectively, so this is what lets either be read as the other.

`Tower.lagda.md` gains `module op-tower`, over the negative hand's
own telescope: `corx`, the embedding condition, the negative cut.
It instantiates `tower⁺` at `opⱽ G` through `op-embedding` and
`duality.op-composable⁺`, and proves two correspondences —
`op-⨾⁺`, that the opposite's positive cut is the negative cut with
its factors exchanged, definitionally; and `op-assoc⁺ f g h :
op.assoc⁺ h g f ≡ sym (assoc⁻ f g h)`. A positive-hand
construction over `tower⁺` transports to the negative hand along
these two.

`Pentagon.lagda.md` gains `module pentagon⁻`, mirroring
`pentagon⁺`'s telescope over `tower⁻`. The proof reads
`pentagon⁺` at `opⱽ G` with the four factors reversed, rewrites
each of the five sides by `op-assoc⁺`, then turns the identity
around with `sym-distr` and reassociates the right leg.
`Core.Groupoid` is a new import there, for `sym-distr` alone.

**State, `verified`.** `gtimeout 300 just check` on
`Bb.VirtualGraphs.Embedding`, `.Tower`, and `.Pentagon`: exit 0
each. `gtimeout 900 just check-tree src/Bb/VirtualGraphs`: 30 of
30 modules typecheck. `just check Bb.index`: exit 0.

---

## 2026-08-05 — a naming pass, against the audit at
`outputs/virtual-graphs-naming-audit.md`

**Renames, `verified`.** Five names conflicted with established
category-theory usage badly enough that a reader taking them at
face value would assume theorems the corpus does not earn. All
five are corrected, source-wide within this tree.

- `half-twist⁻`/`half-twist⁺` → `rx`/`corx`, everywhere. Neither carries a
  ribbon-half-twist or naturality claim; `rx` continues
  `Bb.VgCategoryShape`'s own name for the same role.
- `Balanced.lagda.md` → `Cancellation.lagda.md` (module
  `Bb.VirtualGraphs.Balanced` → `.Cancellation`, internal `module
  balanced` → `module cancellation`). The tree has no tensor and no
  braiding, so "balanced monoidal category" was never statable
  here, and `pair⁺`/`pair⁻` refute the fragment that could be
  stated.
- `is-invertible⁻`/`is-invertible⁺` → `is-absorbing⁻`/
  `is-absorbing⁺`, matching the `absorb⁻`/`absorb⁺` lemmas already
  downstream. The tier gives one-sided absorption, never a
  two-sided inverse.
- `Stability.lagda.md` → `Embedding.lagda.md` (module
  `Bb.VirtualGraphs.Stability` → `.Embedding`), `is-stable` →
  `reflect-is-embedding`, and every derived name along with it
  (`op-embedding`, `embedding-from-injective`,
  `embedding-from-hom-sets`, `embedding-from-contr-cut⁻`,
  `contr-from-embedding`, `reflect-is-embedding-unfolds`). The
  predicate is definitionally `is-embedding reflect`; the old name
  borrowed the least related sense of the single most overloaded
  adjective available.
- `is-interchanging` → `cuts-agree`, `full-interchange` →
  `full-cuts-agree`, `judgment-interchange` → `judgment-cuts-agree`,
  `interchange→involutive` → `cuts-agree→involutive`. None of these
  states the 2-categorical interchange law; all state that the two
  hands' compositions agree. `Aligned.lagda.md`'s own bare
  `interchange` theorem is renamed `hands-agree`, kept distinct from
  `Interchange`'s judgment-level `cuts-agree` to avoid a scope
  clash between the two.
- `Aligned.lagda.md` → `Diagonal.lagda.md` (module
  `Bb.VirtualGraphs.Aligned` → `.Diagonal`, internal `module
  aligned` → `module diagonal`). The old name stated the hypothesis
  (readback aligned with the chosen edge); the new one states what
  distinguishes the module — the diagonal framing `rx = corx`, the
  condition under which the two-hand theory collapses to one
  category. `Diagonal.lagda.md`'s opening paragraph now says so
  outright.

One correctness bug surfaced during the pass, independent of
naming philosophy: `Groupoid/Path.lagda.md` and
`Group/Abelian.lagda.md` both named each cut for the half-twist it
mediates with, inverting this tree's own rule (`Framing.lagda.md`:
the positive cut mediates with the negative half-twist). Both are
corrected — `Group/Abelian.lagda.md`'s fix also required swapping
`cut⁻-is-half-twisted`/`cut⁺-is-half-twisted`, which had baked in the old,
inverted correspondence.

"Invertibility" and "invertible" as descriptive prose (not just the
renamed identifiers) are swept to "absorption"/"absorbing"
throughout, for the same reason as the identifier rename. The
opening paragraphs of `Cancellation`, `Diagonal`, `Circle.Model`,
`Polarity`, `Presentation`, `Bool.Readers`, `Bool.Heap`, and this
tree's own `README.md` are reworded to drop "balanced" and
"aligned" as descriptive words, not only as identifiers. Prose use
of "stability"/"stable" and generic "half-twist" as informal descriptive
words (distinct from the renamed identifiers) is not swept in this
pass — it is widespread enough to be its own undertaking, and is
left as an open question rather than decided silently.

**State, `verified`.** `gtimeout 280 just check-tree
src/Bb/VirtualGraphs`: 30 of 30 modules typecheck, run repeatedly
through the pass and finally after it landed.

---

## 2026-08-04 — a TODO.md, and the Aligned prose names its destination

**Documents.** `Aligned.lagda.md`'s opening paragraph stated the
diagonal-framing construction and its theorems but never named
what they add up to. Added one sentence: interchange collapses the
two hands to one composition, so the graph carries an ordinary
category. `TODO.md` is new, four open items general enough to
outlive the live definition's current shape — a literature pass on
one-sided unitality, and three literature-vendoring tasks. This
tree is the one exception to the namespace's no-open-item-list
rule (`src/Bb/CLAUDE.md`), since it is the live consolidation
target rather than a frozen stratum.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Aligned`: exit 0.

---

## 2026-08-04 — the parity origins share one reflection

**Bool.Heap, `verified`.** `Bb.VgCategoryShape.Parity`'s
`same-reflection` (`Parity.lagda.md:183-187`) compared
`heap false .reflect` against `heap true .reflect`, two separately
bundled record instances. Here the redundancy the old lemma closed
never opens: `HB` is the one graph both `at false` and `at true`
align, so what `same-reflection` proved by `refl` is definitional,
not a separate theorem. The module prose now says so, at the
aligned-telescope section.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Bool.Heap`: exit 0.

---

## 2026-08-04 — the engine, the unit shape, and the models

**Sixteen modules, `verified`.** The chosen-edge theory and the
committed-source model modules landed, closing the
committed-source consolidation. The source ↔ module mapping:

- `Engine` (group H): `Cat.Logic.Gist.ReflectFiber` entire
  (vocabulary, composability with the distribution laws, the
  fiber-contractibility engine, per-hand associativity and unit
  laws) and `Cat.Logic.Gist.RxDict` entire (the reflexive-graph
  dictionary, both hand fibrations, the involution suite), their
  shared inline carrier dissolved into `(G) (idn)`.
- `UnitShape`: the `Bb.NaiveVirtualGraph` unit-identification
  analysis — `Gist.StabilityShape` entire (the datum is a path in a
  hom type; propositionality is a truncation condition, for one
  hand and for the both-hands fiber) and `Gist.SelfUnit`'s
  self-referential datum with its path-groupoid collapse.
- `Word.Carrier`, `Word.Model`, `Word.Defect`, `Word.Polarity`:
  `Cat.Logic.Gist.BalancedWord` (descriptor machinery; the `BW`
  instance, stability, cuts, tiers, winding grade, measurement
  rows), `Cat.Logic.Gist.AssociatesDefect` entire, and the word
  rows of `PolarityHLevel`/`PolarityTwist`/`PolarityCollapse` —
  `Word.Polarity` splits the polarity rows out of §6's
  `Word.Model`.
- `Circle.Model`, `Circle.Thunkable`, `Circle.Polarity`,
  `Circle.Torsor`, `Circle.Shift` (`--cubical`, an import island):
  `Cat.Logic.Gist.ThunkableSquare`'s circle carrier and witness
  rows, `PolarityHLevel`'s circle rows,
  `Cat.Logic.Gist.ReadbackTorsor` entire,
  `Cat.Logic.Gist.ReadbackShift` entire (the retuning rows read as
  one carrier with two readback witnesses).
- `Bool.Klein`: `Bb.OneTwist.Cancel`'s countermodel, run through
  `Extraction`. `Bool.Heap`: `Bb.VgCategoryShape.Parity`, run
  through `Aligned` at each origin. `Bool.Readers`:
  `Bb.WeakDeductiveSystem.Gist.AssociatesCountermodel`'s projection
  and four-reader models plus `Cat.Logic.Gist.BalancedProfile`'s
  `attempt₁`/`attempt₂`.
- `Groupoid.Path`: `Bb.WeakDeductiveSystem.Gist.FramedCut` entire
  plus `Bb.OneTwist.Models`' path model as the one-half-twist instance.
- `Group.Abelian`: `Bb.WeakDeductiveSystem.Gist.FramedGroup` entire
  (including `univalent→prop` via `rxgraph`) plus
  `Bb.OneTwist.Models`' group model as the one-half-twist instance.

Skipped as `Test.*`-only, per the committed-source rule: `Monoid`
(SpikePinningMonoid), `Bool.Endo`, `Bool.Sleeve`,
`Word.Mediation`/`Census`/`Recognition`,
`Circle.Natural`/`Mediation`/`Recognition`. Deferred within the
Engine stage, catalogued in the plan §4.12: the remaining
`Bb.NaiveVirtualGraph` rows beyond `UnitShape` (`UnitCanonical`,
`CrossedUnit`, `AbsorbObstruction`, `DeductiveSystem`'s route
suite, `StableFiber`, `ReflexiveVG`, `PerHandUnit`, the
`JudgmentLens`/`TwoSided` displayed-carrier rows). Thirty modules
in the tree.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.<Mod>`: exit 0 for each of the sixteen. No lemma
omitted anywhere. `Bb.index` gained the sixteen imports;
`just check Bb.index`: exit 0. No `--erased-cubical` module imports
the circle island.

**Documents.** `README.md` updated to the thirty-module shape.

---

## 2026-08-04 — the presentation and the reflexive-graph dictionary

**Three modules, `verified`.** `Presentation` is group P, from
`Cat.Logic.Gist.OperatorCarrier` entire: the `presentation` record
dissolved into a flat twelve-parameter telescope, the carrier and
readback as constructions, all four tier fibers inhabited with
forced edges, the `residue` and its hom-set discharge, the balanced
layer satisfying every law (`presented`, with `op-cross` on the
nose), the graph round trip closing outright on the minimal carrier
with `readback-square` as the readback leg's whole obligation, the
operator dictionary, and the presentation round trip (`round`).
`Graph` and `Display` are group X, from `Cat.Logic.Graph` and
`Cat.Logic.Display`: the framing as two reflexive graphs on one
graph, the fan-calculus dictionary, the two-sided base, the argument
families as univalent lenses, the coslice fibration with push the
cut and lift the witness, the cospan reading of interchange, and
`bipush-comp`. Both import the live `Core.Rx.*` — the tree's one
live dependency beyond `Core` basics and the same one
`Bb.WeakDeductiveSystem.Graph`/`.Display` carry. Fourteen modules in
the tree.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Presentation` / `.Graph` / `.Display`: exit 0 each.
`Bb.index` gained the three imports.

**Documents.** `README.md` rewritten to the fourteen-module shape:
the module map, the consolidation provenance, and the `Core.Rx.*`
live-dependency note.

Next: the model modules (`Word.*`, `Circle.*`, `Bool.*`,
`Groupoid.Path`, `Group.Abelian`), per the extended plan §6.

---

## 2026-08-04 — interchange, the extraction, and the aligned edge

**Three modules, `verified`.** `Interchange` dissolves
`Cat.Logic.Gist.FramedInterchange`'s `framed` record into the frame
theory over readback and two contractible cuts (frame laws,
involutivity forcings, mixed associativity via readback, the
cancellation reduction, the `readable` suite), and adds the
interchange-hypothesis results of
`Bb.WeakDeductiveSystem.Gist.NeutralUnit` and the tortile
transcription of `.Gist.TwistFidelity` over the tower with the pin/K
hypotheses. `Extraction` is group O, from `Bb.OneTwist.Base` and the
general part of `.Cancel`: the negative tier's centre defines the
positive half-twist, its unit laws come free, and the term-side
cancellation is equivalent to centre agreement. `Aligned` is group
V, from `Bb.VgCategoryShape` entire minus its model: the h-category
theory record-free — readback-route left-cancellability, the unit
package pinning `rx` to the extracted unit, all four unit laws,
interchange and stability as theorems, per-hand associativity, and
the contractibility of the neutral-idempotent type. Eleven modules
in the tree.

**State, `verified`.** `gtimeout 300 just check
Bb.VirtualGraphs.Interchange` / `.Extraction` / `.Aligned`: exit 0
each. `Bb.index` gained the three imports; `just check Bb.index`:
exit 0.

Next: `Presentation` (group P), then `Graph`/`Display` (group X);
the model modules wait for their own pass.

---

## 2026-08-04 — the general theory, groups A through D′

**Seven modules, `verified`.** The committed-source consolidation
landed the general theory in dependency order: `Stability` (group A:
representability, stability, the carrier opposite), `Framing` (group
B split as `framing⁻`/`framing⁺`/`framing` along which half-twist each
definition reads, with the duality suite), `Tower` (group C:
`tower⁺` over `half-twist⁻`+S+C⁺ alone, `tower⁻` dually, `tower` with the
mixed word, `associates` and closures, the coherence square,
`collapse⁺/⁻` with the crossed pairing explicit, plus the
`absorption`/`unital` pin-K route), `Pentagon` (over `tower⁺` only),
`Polarity` (definitions, generation, unit-law converses), `Readback`
(group D: hands, near unit laws, residues, stability from the
contractible negative cut), `Balanced` (group D′: centres,
cancellations, far laws, `at-strength`, the polarity collapse).
Sources: `Cat.Logic.Type`/`Base`, `Cat.Logic.Gist.BalancedBase`/
`BalancedProfile`/`ThunkableSquare` (general part)/`PolarityHLevel`/
`PolarityTwist`/`PolarityCollapse`, and
`Bb.WeakDeductiveSystem.Base` for the pin-K route. Eight modules in
the tree.

**State, `verified`.** `gtimeout 300 just check <Mod>`: exit 0 for
each of the seven, in order, after each landing. `Bb.index` gained
the seven imports.

Next: `Interchange`, `Presentation`, `Engine`, `Graph`/`Display`,
`Extraction`, `Aligned`, then the model modules, per the extended
plan (`outputs/.plans/virtual-graphs-vendor.md` §6).

---

## 2026-08-04 — the tree opened with the carrier

**The port, `verified`.** `Type` arrived from `Test.NewDs.Carrier`,
mathematical content unchanged. The module name and the opening
prose changed, nothing else. One module in the tree. `README.md` and
this file opened to the common format of `src/Bb/CLAUDE.md`.
`Bb.index` gained the tree's import.

**State, `verified`.** `just check Bb.VirtualGraphs.Type`: exit 0.
`just check Bb.index`: exit 0.

Next: the tree receives the consolidated virtual-graph results, per
the plan at `outputs/.plans/virtual-graphs-vendor.md`.
