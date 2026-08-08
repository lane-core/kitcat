# Surface audit: `Bb.NaiveVirtualGraph` against `Bb.VirtualGraphs`

Read-only inventory. Every `.lagda.md` file under `src/Bb/NaiveVirtualGraph/`
checked identifier-by-identifier against `src/Bb/VirtualGraphs/UnitShape.lagda.md`
(the tree's one cited destination) and, where content looked related, against
the general theory modules `Stability`/`Framing`/`Tower`/`Readback`/`Balanced`/
`Engine`, plus `Graph`/`Display`/`Groupoid.Path`/`Extraction`.

Full file inventory (`find src/Bb/NaiveVirtualGraph -type f`):

```
src/Bb/NaiveVirtualGraph/Base.lagda.md
src/Bb/NaiveVirtualGraph/CHANGELOG.md
src/Bb/NaiveVirtualGraph/README.md
src/Bb/NaiveVirtualGraph/Gist/AbsorbObstruction.lagda.md
src/Bb/NaiveVirtualGraph/Gist/CrossedUnit.lagda.md
src/Bb/NaiveVirtualGraph/Gist/DeductiveSystem.lagda.md
src/Bb/NaiveVirtualGraph/Gist/JudgmentLens.lagda.md
src/Bb/NaiveVirtualGraph/Gist/PathGroupoid.lagda.md
src/Bb/NaiveVirtualGraph/Gist/PerHandUnit.lagda.md
src/Bb/NaiveVirtualGraph/Gist/ReflexiveVG.lagda.md
src/Bb/NaiveVirtualGraph/Gist/SelfUnit.lagda.md
src/Bb/NaiveVirtualGraph/Gist/StabilityShape.lagda.md
src/Bb/NaiveVirtualGraph/Gist/StableFiber.lagda.md
src/Bb/NaiveVirtualGraph/Gist/TwoSided.lagda.md
src/Bb/NaiveVirtualGraph/Gist/UnitCanonical.lagda.md
```

Twelve `Gist` modules plus `Base`, matching the tree's own README/CHANGELOG
count. The CHANGELOG's deferred list (`UnitCanonical`, `CrossedUnit`,
`AbsorbObstruction`, `DeductiveSystem`, `StableFiber`, `ReflexiveVG`,
`PerHandUnit`, `JudgmentLens`, `TwoSided` — nine names) is exhaustive: it
covers every `Gist` module except `StabilityShape` and `SelfUnit`. `Base`
is named in neither the vendored nor the deferred list.

---

## `Base.lagda.md`

**Content.** The chosen-edge carrier record `virtual-graph` (`ob`, `hom`,
`idn`, `reflect`), the `sequents`/`vocab` modules building `term`/`coterm`/
`argument`/`var`/`covar`/`coact-π`/`act-π`/`coact`/`act`/`readback`, and a
free-standing generic lemma `module pin` (`pin-contr`, lines
`src/Bb/NaiveVirtualGraph/Base.lagda.md:134-190`): given an operator `T` on
paths and a pin `t₀` at `refl`, the package of a `readback`-shaped family
together with an identification of its refl-component with `t₀` is
contractible, by retracting onto a singleton anchor.

**Verdict — vocabulary: MOOT/SUPERSEDED.** `Bb.VirtualGraphs.Type` drops
`idn` from the carrier record entirely (`ob`, `hom`, `reflect` only —
`src/Bb/VirtualGraphs/Type.lagda.md:21-43`), and `Bb.VirtualGraphs.Degenerate.Chosen`'s
`module chosen` (`src/Bb/VirtualGraphs/Engine.lagda.md:41-79`) reconstructs
`var`/`covar`/`argue`/`intro`/`elim`/`eval`/`coact-π`/`act-π`/`coact`/`act`/
`composite⁻`/`composite⁺` with `idn` as an external function parameter
instead of a record field. Every definition `Base` states over the baked-in
`idn` has a definitionally identical counterpart in `chosen`. This is a
structural change (field → parameter), not a content gap.

**Verdict — `module pin`: UNVENDORED-UNIQUE.** No module under
`Bb.VirtualGraphs` invokes a generic pinned-retract lemma of this shape.
Every site that needs the special case (`UnitShape.shape.singl-contr`,
`src/Bb/VirtualGraphs/UnitShape.lagda.md:57-59`) reimplements it ad hoc by
direct singleton contraction rather than instantiating `Base`'s `pin`
module. The general lemma itself is not reproduced anywhere in the tree.

---

## `Gist/StabilityShape.lagda.md` — VENDORED

Per the CHANGELOG, into `Bb.VirtualGraphs.UnitShape`, `module shape`.
Definition-by-definition:

| StabilityShape (`Gist/StabilityShape.lagda.md`) | UnitShape (`UnitShape.lagda.md`) |
| --- | --- |
| `unit⁻` :47 | `unit⁻` :51 |
| `datum` :49-50 | `datum` :54-55 |
| `singl-contr` :59-61 | `singl-contr` :57-59 |
| `reassoc` :63-68 | `reassoc` :61-66 |
| `component≃path` :70-74 | `component≃path` :68-72 |
| `datum≃path` :76-77 | `datum≃path` :74-75 |
| `datum-prop→loop-prop` :90-92 | `datum-prop→loop-prop` :82-84 |
| `datum-prop→truncation` :94-98 | `datum-prop→truncation` :86-90 |
| `unit⁺` :112-113 | `unit⁺` :104-105 |
| `singl-contr⁺` :115-117 | *(absent — see below)* |
| `reassoc⁺` :119-124 | `reassoc⁺` :107-112 |
| `component≃path⁺` :126-130 | `component≃path⁺` :114-118 |
| `both` :132-133 | `both` :120-121 |
| `both-reassoc` :135-139 | `both-reassoc` :123-128 |
| `both≃path` :141-143 | `both≃path` :130-132 |
| `both-contr→truncation` :152-156 | `both-contr→truncation` :134-138 |

One gap, harmless: `singl-contr⁺` in the source is a byte-identical
duplicate of `singl-contr` (compare `Gist/StabilityShape.lagda.md:59-61`
and `:115-117`). `UnitShape` deduplicates — the outer `singl-contr`
(`:57-59`) is reused directly at `component≃path⁺` (`:116`) instead of
being redefined. No mathematical content is missing; this is a
simplification the vendoring made, not an omission.

The closing prose's "two limits on the claim" discussion (the packaging
bound, and the open question about h-level three) is not restated in
`UnitShape`'s prose, but `UnitShape`'s opening paragraph carries the load-
bearing conclusion (`datum≃path` computes the datum as a hom-type path, so
propositionality is a truncation condition).

**Gaps: none at the identifier level.**

---

## `Gist/SelfUnit.lagda.md` — VENDORED

Per the CHANGELOG, into `Bb.VirtualGraphs.UnitShape`, `module self` and
`module self-path`.

| SelfUnit (`Gist/SelfUnit.lagda.md`) | UnitShape (`UnitShape.lagda.md`) |
| --- | --- |
| `pre-graph` record :37-59 | *(elided — see below)* |
| `argue` :69-70 | *(elided — inlined pairing)* |
| `unit-data` :72-76 | `unit-data` :151-155 |
| `is-unital` :78-79 | `is-unital` :157-158 |
| `module path` / `PG` :89-101 | *(reuses `Bb.VirtualGraphs.Groupoid.Path`, see below)* |
| `term-contr` :108-110 | reused via `open path ... using (... term-contr ...)` :173 |
| `coterm-contr` :112-114 | reused via same `open` :173 |
| `collapse⁺` :116-120 | `collapse⁺` :178-185 |
| `collapse⁻` :122-126 | `collapse⁻` :186-192 |

The `pre-graph` record (a graph with no chosen edge, built to let the
self-referential datum be stated without `idn` in scope) is not
reconstructed as a separate type in `UnitShape`; `module self`
(`UnitShape.lagda.md:149-158`) instead takes the ordinary `virtual-graph G`
from `Bb.VirtualGraphs.Type` and simply never uses its `reflect`-only
vocabulary's absent `idn`-dependence — `Type`'s carrier already lacks `idn`,
so `pre-graph` was made redundant by the same carrier change noted for
`Base` above. `argue`'s pairing is inlined rather than named.

`module self-path`'s path-graph model reuses the general framed
path-groupoid infrastructure — `open path {A = A} (λ _ → refl) (λ _ →
refl) using (PG; emb; term-contr; coterm-contr)`
(`UnitShape.lagda.md:173-174`), importing `Bb.VirtualGraphs.Groupoid.Path`
— instead of SelfUnit's bespoke `pre-graph`-based `PG`. This `path` module
was itself vendored from `Cat.Logic.Gist.ThunkableSquare`/`Bb.WeakDeductive
System.Gist.FramedCut`/`Bb.OneTwist.Models` per the CHANGELOG's `Groupoid.
Path` entry, not from `SelfUnit` — SelfUnit's specific one-twist
instantiation (`idn = refl` on both hands) is exactly the `(λ _ → refl)
(λ _ → refl)` call in `UnitShape`, so the two `collapse⁺`/`collapse⁻`
statements and proofs are the same construction, reached through the
already-vendored general machinery rather than reproduced standalone.

**Gaps: none at the identifier level** (the `pre-graph` record and `argue`
helper are structural elisions, not lost content).

---

## `Gist/UnitCanonical.lagda.md` — UNVENDORED-UNIQUE

**Content.** Given the unit tier (fiber form) alone plus a bare `readback`
family — with **no composability assumed anywhere** — `module canonical`
(`Gist/UnitCanonical.lagda.md:134-181`) derives `unit⁻-is-idn`/`unit⁺-is-
idn` directly (`sym (rb (unit⁻ x)) ∙ unit⁻-absorb x (covar x)`, :146-150)
and hence `units-agree`, `idn-absorb⁻`/`idn-absorb⁺`, and uniqueness. A
second module (`module stability`, :197-259) builds the readback-torsor-
plus-flank-coherence packaging (`is-stable`) and proves it a proposition.
A third section (`## The half-adjoint form, and why it fails`, :274-339)
proves that *dropping* the `is-contr` wrapper — asking the readback-plus-
coherence pair itself to be a proposition — forces every twist vanishing
on endomorphisms to be trivial, a truncation condition; `half-adjoint-
forces-truncation` (:329-339) is the theorem.

**Verdict.** `Bb.VirtualGraphs.Degenerate.Engine`'s readback-free route
(`src/Bb/VirtualGraphs/Engine.lagda.md:136-250`) derives the same kind of
absorption/uniqueness facts from unit-fiber contractibility **plus**
composability — it explicitly does not need readback (docstring, `Engine.
lagda.md:1-13`: "no readback, no interchange, and no stability
hypothesis"). `UnitCanonical`'s minimal argument runs the other way:
readback alone, **no composability**. No module under `Bb.VirtualGraphs`
derives the canonical-unit identification from bare readback without a
composability hypothesis; the committed theory took the composability
route instead (`Engine`) and never revisited the readback-only one. The
half-adjoint/truncation theorem (`half-adjoint-forces-truncation`,
:329-339) — a distinct, load-bearing negative result about what happens if
`is-stable`'s `is-contr` wrapper is dropped — has no counterpart anywhere
in `Bb.VirtualGraphs`; `Stability.lagda.md`'s own `is-stable` is a
different notion entirely (propositional fibers of `reflect`, not
contractibility of a readback-coherence pair), so the question this
section answers does not even arise there in the same form.

---

## `Gist/CrossedUnit.lagda.md` — UNVENDORED, partially covered elsewhere

**Content.** Takes the two axiom halves apart: the coterm-hand's unit
fiber (`is-unital⁻`, :43-44) produces a filler `unit⁻`, and the *derived*
`covar⁻ y = y , unit⁻ y` (:61-62) — not a second independently chosen
family — fills the term-hand's coterm slot (`act-π⁻`, :64-65). The "crossed
fixpoint" result `crossed` (:267-268) shows an **arbitrary** family `a`
(no absorption law assumed, no h-level on the carrier) is forced to equal
the term-hand's canonical unit, via the "exchange" hypothesis
(`exchange-hypothesis`, :143-146) and a path-groupoid instance
(`module path`, :161-239) where the exchange holds unconditionally.

**Verdict.** `Bb.VirtualGraphs.Degenerate.Extraction`'s `module system⁻`
(`src/Bb/VirtualGraphs/Extraction.lagda.md:76-111`) covers the same broad
shape — a second unit (`centre⁺`) derived from the first (`twist⁺`, itself
extracted from `U⁻`'s centre), with an `agree`/`cancel⁺` equivalence
(:99-110) playing the role `CrossedUnit`'s `crossed` plays. But `Extraction`
needs `is-stable` and `is-composable⁺`/`is-composable⁻` (:76-77) to get
there; `CrossedUnit`'s core result needs **neither** — it is a fact about
an arbitrary family over the bare carrier, proved through composability-
free fiber contraction alone (its own `module _ {o h} (G ...) (U⁻ ...)`,
:53-76, and the path-groupoid witness, :161-239). That composability-free,
h-level-free generality is not reproduced by `Extraction` or anywhere else
checked. Net: the *conclusion under composability* is covered
(`Extraction`); the *stronger, hypothesis-free* argument is
UNVENDORED-UNIQUE.

---

## `Gist/AbsorbObstruction.lagda.md` — UNVENDORED-UNIQUE

**Content.** A rigidity theorem: any **propositional** predicate `P` on
`(ob, hom, idn, reflect)` that delivers absorption (`absorbs`, :49-50)
forces the "doubling" endomap of the reflexivity-loop family to be trivial
on `π₀` of `Ω²` (`doubling-rigid`, :161-163), by perturbing `idn` along a
self-loop (`perturb`, :63-69) and sliding a propositional witness along
it (`drift`/`rigid`, :89-101). At the path groupoid on `S²` — CONJECTURED,
not machine-checked here — the generator of `π₂` gives a nontrivial
doubling-endomap section, so no such propositional predicate exists there
at all; absorption itself is freely available (`pg-absorbs`, :128-130), so
the obstruction is specifically to a *propositional route* to it.

**Verdict.** This result is tied intrinsically to the `Base`-style carrier
where `idn` is a **free field** that can be perturbed independently of
`reflect` (`perturb`, :63-69 — `ob`, `hom`, `reflect` untouched, only `idn`
varies). `Bb.VirtualGraphs`'s committed theory never carries a chosen edge
as a record field at all — `twist⁻`/`twist⁺` are always external
parameters to `Framing`/`Tower`/etc. — so the specific perturbation
argument does not directly transfer, and no analogous rigidity theorem
appears anywhere checked. The underlying moral (propositional wrappers
need `is-contr`, not bare truncation, or they force triviality) is the
same one `UnitCanonical`'s half-adjoint section and `StabilityShape`'s
truncation lemmas rely on, but as a *file* this rigidity argument and its
`S²` model are unique and not restated.

---

## `Gist/DeductiveSystem.lagda.md` — UNVENDORED-BUT-COVERED-ELSEWHERE (Engine)

**Content.** Packages the whole predicate as three records
(`is-composable`, `is-unital`, `is-stable`/`is-deductive-system`,
:55-98, 84-133, 349-364) plus full propositionality proofs (:307-337), and
an "Appendix — the tiers in `Core.Rx` terms" (:339-503) building `coslice`/
`slice` displays, `coslice-is-fibration`/`slice-is-fibration`, and
`push-is-comp`/`pull-is-comp` (:381-410) plus `term-disp`/`coterm-disp`
fibrations (:467-503).

**Verdict.** `Bb.VirtualGraphs.Degenerate.Chosen`'s `module chosen`/`module
composable`/`module engine` (`Engine.lagda.md:41-208`) derives the
readback-free unit⁻/unit⁺ (fiber form, identical to `DeductiveSystem`'s
`is-unital`), absorption, and uniqueness — **and, unlike
`DeductiveSystem`, also derives associativity and both unit laws**
(`assoc⁻`/`assoc⁺`/`unitr⁻`/`unitl⁺`, `Engine.lagda.md:216-251`), which
`DeductiveSystem` never attempts. Engine's `module dict`
(`Engine.lagda.md:261-370`) then reproduces the appendix's fibration
dictionary essentially one-to-one: `coslice`/`coslice-fibration`/
`push-is-comp` (`Engine.lagda.md:332-343`) match `DeductiveSystem`'s
`coslice`/`coslice-is-fibration`/`push-is-comp`
(`Gist/DeductiveSystem.lagda.md:381-405`); `slice`/`slice-fibration`/
`pull-is-comp` match likewise. The specific *bundling* —
`is-deductive-system` as one record with a readback-plus-coherence
`is-stable` field and a field-by-field propositionality proof — has no
literal counterpart, since `Bb.VirtualGraphs.Stability`'s `is-stable`
is the unrelated "embedding" notion (`Stability.lagda.md:62-63`). The
substance is superseded by Engine's strictly more general, strictly
stronger (associativity included) readback-free result; the specific
record shape and its `is-prop` proof are not reproduced.

---

## `Gist/StableFiber.lagda.md` — UNVENDORED-BUT-COVERED-ELSEWHERE (Engine, Stability)

**Content.** A different unit packaging — each hand's action **at the
chosen edge is an equivalence** (`eqv⁻`/`eqv⁺`, :88-89) together with
idempotence of the reflected edge's self-composite (`rep-idem⁻`/
`rep-idem⁺`, :90-91) — from which absorption is derived by cancelling the
equivalence against the idempotence (`idn-absorb⁻`/`idn-absorb⁺`,
:113-127), readback-free. Also: `is-stable` recast as `is-equiv restrict`
(:393-394), and a full `opⱽ` opposition dictionary (:199-263) with
`composable-op`/`unital-op`/`stable-op` and their involutions.

**Verdict.** The readback-free-absorption *conclusion* is exactly what
`Bb.VirtualGraphs.Degenerate.Engine`'s `module engine` reaches (see `DeductiveSystem`
entry above), via a different technical packaging (unit-fiber
contractibility, not action-is-equivalence-plus-idempotence). The two are
not the same proof, but they establish the same fact about the same
carrier shape. `StableFiber`'s `opⱽ` (`Gist/StableFiber.lagda.md:199-206`)
is a **field-for-field identical** construction to `Bb.VirtualGraphs.
Stability`'s own `opⱽ` (`Stability.lagda.md:99-105`) and
`opⱽ-invol`/`op-stable` (`Stability.lagda.md:104-119`) — same record, same
swap, same involution proof. The `is-stable = is-equiv restrict` framing
(:393-394) is not reproduced verbatim anywhere, but `Groupoid.Path.PG-
stable` (`Groupoid/Path.lagda.md:103-104`) proves the analogous fact
(`Stability`'s embedding-style `is-stable`) unconditionally at the path
groupoid, covering the model witness this file was building toward.

---

## `Gist/ReflexiveVG.lagda.md` — UNVENDORED-UNIQUE, MOOT

**Content.** A different carrier design: `reflexive-virtual-graph` bakes
the two absorption laws in **as fields** (`absorb⁻`/`absorb⁺`,
:76-78) rather than deriving them from a fiber or an equivalence, making
`is-composable`/`is-unital`/`is-stable` trivially contractibility-or-
`is-equiv` statements with no argument required (:179-211).

**Verdict.** No module under `Bb.VirtualGraphs` bakes absorption in as a
carrier field; `Framing`/`Tower`/`Engine` always treat `twist⁻`/`twist⁺`
as external parameters and always *derive* absorption (from a fiber, an
equivalence, or a cut), never postulate it. This design is genuinely
unreproduced. It is also the tree's own explicitly marked dead end: the
README (`src/Bb/NaiveVirtualGraph/README.md:35-36`) calls it one of "two
spikes [that] take the remaining routes," and the provenance section
records the whole tree, this file included, as "superseded rather than
promotable" once the twist-framed carrier arrived
(`README.md:51-58`). Unvendored and not a gap to close — the committed
theory deliberately did not go this way.

---

## `Gist/PerHandUnit.lagda.md` — UNVENDORED-BUT-COVERED-ELSEWHERE (technique matches StableFiber/Engine)

**Content.** A yet more generic restatement, over a bare `reflexive-graph`
(`vtx`/`edge`/`rx`) and an abstract ternary `emb` primitive rather than
`virtual-graph`'s `reflect`: two hand-local compositions `⨾▿`/`⨾▵`
(`module hands`, :83-97), each hand's absorption from idempotence-at-`rx`
plus an equivalence hypothesis (`module unital`, :119-155), readback-free.
Explicitly leaves the cross-hand agreement `flank-pin`
(`flank▿ ≡ flank▵`, :198-199) **uninhabited** — flagged as "the cell the
stability tier pins," i.e., the one fact this file does not supply.

**Verdict.** The absorption-from-idempotence-and-equivalence technique is
the same one `Gist/StableFiber.lagda.md` uses (see above), restated at one
more level of genericity (an arbitrary `emb`, not `virtual-graph`'s
`reflect`). That technique's downstream consequences are covered by
`Engine`/`Stability` as discussed there. The explicit "`flank-pin` is a
type, uninhabited by design" observation — documenting exactly what
stability adds beyond the two one-hand absorptions — has no literal
counterpart, though `Bb.VirtualGraphs.Degenerate.Readback`'s `module residues`
(`Readback.lagda.md:116-151`, "The four absorption hypotheses do not
follow from readback... each hypothesis is exactly a missing far unit law
or a crossed pairing") makes a structurally similar point about a
different (readback-based, not idempotence-based) construction.

---

## `Gist/JudgmentLens.lagda.md` — UNVENDORED, partially covered elsewhere

**Content.** Displays `judgment` (contravariant/covariant mixed variance)
over the **one-sided** base via `Core.Rx.Lens`'s `unbiased-lens`
(`judgment-lens`, :132-139, fields `linj`/`rinj`/`munitor`/`runitor`), then
a second `unbiased-lens` on `hom` itself (`hom-lens`, :259-266) whose two
unitors are the two unit laws derived from readback + composability
(`unitr⁻`/`unitl⁺`, :247-257). Discusses (with a source citation,
`resources/sterling-reflexive-graph-lenses`) the pitfall of a lens
carrying both a lax and an oplax unitor. Ends with `virtual-graphᴰ`, a
Σ-by-Σ "displaced" sequent calculus (:301-357).

**Verdict.** No module under `Bb.VirtualGraphs` uses `unbiased-lens` at
all — `Display.lagda.md` and `Graph.lagda.md` (the committed lens content,
sourced from `Cat.Logic.Graph`/`Cat.Logic.Display`, not from
`NaiveVirtualGraph`) use only `oplax-cov-lens`/`lax-ctrv-lens` over the
**two-sided** base (`rx.binary-product`). The specific one-sided
`unbiased-lens` construction, the `virtual-graphᴰ` displaced calculus, and
the Sterling citation/discussion are UNVENDORED-UNIQUE. The `hom-lens`'s
two unit laws are, in substance, what `Bb.VirtualGraphs.Degenerate.Readback`'s
`hand⁺`/`hand⁻` modules derive in the twist-framed setting
(`unitr⁺`/`unitl⁻`, `Readback.lagda.md:46-52, 74-79`) — same shape of
result (a unit law per hand, from a cut plus readback), different
carrier/vocabulary.

---

## `Gist/TwoSided.lagda.md` — UNVENDORED-BUT-COVERED-ELSEWHERE (Graph, Display — close match)

**Content.** Builds the two-sided base as `rx.binary-product (rx.op
graph) graph` (`two-sided`, :68-69), the joint action `bipush`
(:90-91), shows it composes with mismatched hands
(`bipush-comp`, :145-152), reads interchange as agreement of two
pushforwards into a common fiber — a **cospan**, not a unitor
(`interchange-is-cospan`/`cospan-is-interchange`, :268-281) — and shows
interchange is equivalent to a **mediation** between the two compositions
(`interchange→mediation`, :296-301). Packages the base's transport as an
`oplax-cov-lens` (`judgment-lens`, :218-224).

**Verdict.** This is the closest match found in the whole deferred set.
`Bb.VirtualGraphs.Graph`'s `module two-sided`
(`Graph.lagda.md:97-122`) builds the identical construction — `base =
rx.binary-product (rx.op graph⁻) graph⁺` (:104), `bipush` (:117-118),
`judgment-fam` (:120-121) — generalized from one twist to two
(`twist⁻`/`twist⁺`). `Bb.VirtualGraphs.Degenerate.Display`'s `bipush-comp`
(`Display.lagda.md:181-187`) is the same mismatched-hands composition
lemma, generalized the same way. Display's `push-is-composite⁺`/
`push-is-composite⁻`/`cospan-from-cuts`/`cuts-from-cospan`
(`Display.lagda.md:144-164`) is the same cospan reading of interchange as
`TwoSided`'s `push-is-composite⁻`/`push-is-composite⁺`/
`interchange-is-cospan`/`cospan-is-interchange` — same diagram, same
argument, twist-framed. Display's `judgment-lens`
(`Display.lagda.md:127-129`) is the same `oplax-cov-lens` packaging. Per
the `Bb.VirtualGraphs` CHANGELOG (`2026-08-04 — the presentation and the
reflexive-graph dictionary` entry), `Graph`/`Display` were sourced from
`Cat.Logic.Graph`/`Cat.Logic.Display`, **not** from `NaiveVirtualGraph` —
so this overlap is exactly the "coincidental" case the task asked to
check for, not a mis-attributed citation. `TwoSided`'s explicit
`mediation`-from-`interchange` theorem (:161-172, 296-301) has no named
counterpart under that exact name in `Graph`/`Display`, though the
underlying cospan fact both files use is the same.

---

## `Gist/PathGroupoid.lagda.md` — UNVENDORED-BUT-COVERED-ELSEWHERE (Groupoid.Path), MOOT in its conditional part

**Content.** Model-inhabitance witness for the one-`idn` `is-deductive-
system`: representability is total at the path groupoid on any type
(`reflect-equiv`, :167-168), giving unconditional `PG-composable`/
`PG-unital`/`readback`/associativity (:180-301) with no h-level hypothesis.
A separate `module groupoid-carrier` (:352-386) proves the bundled,
readback-plus-coherence `is-stable` propositional **when the carrier is a
groupoid** (`is-groupoid A`), and assembles `PG-deductive`.

**Verdict.** `Bb.VirtualGraphs.Groupoid.Path`'s `module one-twist`
(`Groupoid/Path.lagda.md:247-277`) is a strict generalization of the
unconditional part: it inhabits the same telescope (stability in the
embedding sense, both composabilities, both invertibility tiers) at an
**arbitrary** loop family `t⁻` (not fixed at `refl`), still with no h-level
hypothesis. `PathGroupoid`'s own `groupoid-carrier` module is specific to
its own bundled `is-stable` notion and is not literally reproduced, but it
is functionally moot: `Groupoid.Path.PG-stable`
(`Groupoid/Path.lagda.md:103-104`) proves the (stronger, embedding-style)
stability **unconditionally**, at every type, obviating the need for a
groupoid hypothesis to get a stable model.

---

## Independent checks

**Step 6 — live-dependency scan.** The task's suggested command
(`rg --type agda`) silently matches nothing, because ripgrep's built-in
`agda` type is `*.agda, *.lagda` and does not include `*.lagda.md` (verified
via `rg --type-list`). Re-run without the type filter:

```
rg -n "open import Bb\.NaiveVirtualGraph|import Bb\.NaiveVirtualGraph" src/ 2>/dev/null | grep -v "^src/Bb/NaiveVirtualGraph/"
```

Output:

```
src/Bb/index.lagda.md:114:import Bb.NaiveVirtualGraph.Base
src/Bb/index.lagda.md:115:import Bb.NaiveVirtualGraph.Gist.AbsorbObstruction
src/Bb/index.lagda.md:116:import Bb.NaiveVirtualGraph.Gist.CrossedUnit
src/Bb/index.lagda.md:117:import Bb.NaiveVirtualGraph.Gist.DeductiveSystem
src/Bb/index.lagda.md:118:import Bb.NaiveVirtualGraph.Gist.JudgmentLens
src/Bb/index.lagda.md:119:import Bb.NaiveVirtualGraph.Gist.PathGroupoid
src/Bb/index.lagda.md:120:import Bb.NaiveVirtualGraph.Gist.PerHandUnit
src/Bb/index.lagda.md:121:import Bb.NaiveVirtualGraph.Gist.ReflexiveVG
src/Bb/index.lagda.md:122:import Bb.NaiveVirtualGraph.Gist.SelfUnit
src/Bb/index.lagda.md:123:import Bb.NaiveVirtualGraph.Gist.StabilityShape
src/Bb/index.lagda.md:124:import Bb.NaiveVirtualGraph.Gist.StableFiber
src/Bb/index.lagda.md:125:import Bb.NaiveVirtualGraph.Gist.TwoSided
src/Bb/index.lagda.md:126:import Bb.NaiveVirtualGraph.Gist.UnitCanonical
```

The only importer anywhere in `src/` outside the tree itself is
`src/Bb/index.lagda.md`, which imports all thirteen modules (`Base` plus
all twelve `Gist` modules) — this is the archive-wide index that keeps
`just check-tree src/Bb` covering the tree, not a live consumer. No module
under `Cat.*`, `Bb.VirtualGraphs`, `Bb.WeakDeductiveSystem`, or elsewhere
imports `Bb.NaiveVirtualGraph`.

**Step 7 — `Bb.index` import status.** Confirmed by the same grep:
`src/Bb/index.lagda.md` still imports all thirteen `Bb.NaiveVirtualGraph`
modules (lines 114–126), unchanged by the `Bb.VirtualGraphs` vendoring.

---

## Summary

**Vendored, essentially complete** (module-level, per the CHANGELOG,
confirmed identifier-by-identifier):

- `Gist/StabilityShape.lagda.md` → `Bb.VirtualGraphs.UnitShape`,
  `module shape`
- `Gist/SelfUnit.lagda.md` → `Bb.VirtualGraphs.UnitShape`, `module self` /
  `module self-path`

**Files still holding unique, unvendored content** (the deliverable this
task was scoped to pin down):

| File | Unique content not found elsewhere in `Bb.VirtualGraphs` |
| --- | --- |
| `Base.lagda.md` | The generic `pin`/`pin-contr` retract lemma (:128-190) — unreused anywhere; the carrier vocabulary itself is superseded by `Type` + `Engine.chosen`. |
| `Gist/UnitCanonical.lagda.md` | The readback-alone (no composability) canonical-unit derivation (:134-181); the half-adjoint/truncation theorem `half-adjoint-forces-truncation` (:329-339). |
| `Gist/CrossedUnit.lagda.md` | The composability-free, h-level-free "crossed fixpoint" generality (:53-76, 161-239) — `Extraction`'s `system⁻` only covers the composability-assuming corollary. |
| `Gist/AbsorbObstruction.lagda.md` | The whole rigidity theorem and its `S²`-model obstruction (:37-205) — tied to the free-`idn`-field carrier shape the committed theory abandoned. |
| `Gist/ReflexiveVG.lagda.md` | The absorption-as-carrier-field design (:37-79) — a deliberately abandoned alternative, per the tree's own README. |
| `Gist/JudgmentLens.lagda.md` | The one-sided `unbiased-lens` construction, `virtual-graphᴰ` displaced Σ-by-Σ calculus (:301-357), and the Sterling lax/oplax citation. |

**Deferred files whose substance is covered elsewhere, though not by
literal vendoring** (the general theory reaches the same conclusions by a
different, usually more general, route):

- `Gist/DeductiveSystem.lagda.md` — superseded by `Bb.VirtualGraphs.Degenerate.Engine`
  (strictly stronger: includes associativity, which `DeductiveSystem`
  lacks; its Rx-dictionary appendix is reproduced near-verbatim in
  `Engine.dict`).
- `Gist/StableFiber.lagda.md` — readback-free absorption covered by
  `Engine` (different unit packaging, same conclusion); `opⱽ` dictionary
  is field-for-field identical to `Bb.VirtualGraphs.Stability`'s.
- `Gist/PerHandUnit.lagda.md` — same absorption-from-idempotence technique
  as `StableFiber`, restated more generically; its `flank-pin` observation
  echoed structurally (not literally) by `Readback.module residues`.
- `Gist/TwoSided.lagda.md` — the closest match of all: `Bb.VirtualGraphs.
  Graph.two-sided` and `Display` reproduce the two-sided base, `bipush`,
  `bipush-comp`, and the cospan reading of interchange almost line for
  line, generalized from one twist to two. Sourced from `Cat.Logic.Graph`/
  `.Display`, not from this file — genuinely coincidental coverage.
- `Gist/PathGroupoid.lagda.md` — its unconditional model-inhabitance
  content is strictly generalized by `Groupoid.Path.one-twist`; its
  groupoid-conditional stability proof is moot given `Groupoid.Path`
  proves the (stronger) embedding-style stability unconditionally.

**Live-dependency status:** No module outside `src/Bb/NaiveVirtualGraph/`
imports it except the archive-wide `src/Bb/index.lagda.md` (all thirteen
modules, lines 114–126, unchanged). Zero live consumers.
