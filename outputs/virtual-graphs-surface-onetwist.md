# Surface audit: does `Bb.VirtualGraphs` cover `Bb.OneTwist`

Content-level check of whether every definition, record field, and
theorem in `src/Bb/OneTwist/` is present — verbatim or as an
equivalent restatement — in `src/Bb/VirtualGraphs/`, against the
mapping `src/Bb/VirtualGraphs/CHANGELOG.md` (2026-08-04, "interchange,
the extraction, and the aligned edge" entry and the "Bool.Klein" /
"Groupoid.Path" / "Group.Abelian" lines of the 2026-08-04 "the engine,
the unit shape, and the models" entry) claims.

## File inventory

```
src/Bb/OneTwist/Base.lagda.md
src/Bb/OneTwist/Cancel.lagda.md
src/Bb/OneTwist/CHANGELOG.md   (process doc, not checked for content)
src/Bb/OneTwist/Models.lagda.md
src/Bb/OneTwist/README.md      (process doc, not checked for content)
```

Three `.lagda.md` files carry mathematical content: `Base`, `Cancel`,
`Models`.

Destination modules in `Bb.VirtualGraphs` referenced by the claimed
mapping: `Extraction.lagda.md`, `Bool/Klein.lagda.md`,
`Groupoid/Path.lagda.md`, `Group/Abelian.lagda.md`. `Extraction`
itself opens the shared vocabulary modules `Type.lagda.md`,
`Stability.lagda.md`, `Framing.lagda.md`, `Tower.lagda.md`; those were
read as well, since the one-twist carrier's generic operations
(`term`, `coterm`, `judgment`, `act`, `coact`, `composite⁺/⁻`,
`is-stable`, `is-composable⁺/⁻`, `is-invertible⁻/⁺`) are what
`OneTwist.Base`'s `graph⁻` record bundles inline, and the
VirtualGraphs tree states that same vocabulary as flat-parameter
modules instead of record fields. Per the CHANGELOG, that general
vocabulary is attributed to a separate, earlier landing (`Stability`
group A, `Framing` group B, `Tower` group C, sourced from
`Cat.Logic.Gist.*` and `Bb.WeakDeductiveSystem.Base`), not to
`OneTwist`. This audit still cites it, because it is where
`OneTwist.Base`'s corresponding definitions actually surface.

## `src/Bb/OneTwist/Base.lagda.md`

**Verdict: FULLY VENDORED.**

`graph⁻`'s bundled fields and derived operations restate, one-for-one,
across `Type`, `Stability`, `Framing`, `Tower`, and `Extraction`:

| `OneTwist.Base` (`file:line`) | `VirtualGraphs` (`file:line`) |
| --- | --- |
| `ob`, `hom` — Base.lagda.md:24-25 | `virtual-graph.ob/hom` — Type.lagda.md:23-24 |
| `term` — Base.lagda.md:27-28 | `virtual-graph.term` — Type.lagda.md:26-27 |
| `coterm` — Base.lagda.md:30-31 | `virtual-graph.coterm` — Type.lagda.md:29-30 |
| `argument` — Base.lagda.md:33-34 | `virtual-graph.argument` — Type.lagda.md:32-33 |
| `conclusion` — Base.lagda.md:36-37 | `virtual-graph.conclusion` — Type.lagda.md:35-36 |
| `judgment` — Base.lagda.md:39-40 | `virtual-graph.judgment` — Type.lagda.md:38-39 |
| `reflect` (field) — Base.lagda.md:43 | `virtual-graph.reflect` (field) — Type.lagda.md:42 |
| `twist⁻` (field) — Base.lagda.md:44 | `extraction`'s `twist⁻` parameter — Extraction.lagda.md:29 |
| `var` — Base.lagda.md:46-47 | `framing⁻.var` — Framing.lagda.md:47-48 |
| `coact-π` — Base.lagda.md:49-50 | `framing⁻.coact-π` — Framing.lagda.md:50-51 |
| `unital⁻` (field) — Base.lagda.md:56-57 | `framing⁻.is-invertible⁻` (as parameter `U⁻`) — Extraction.lagda.md:30 |
| `twist⁺` — Base.lagda.md:59-60 | `extraction.twist⁺` — Extraction.lagda.md:34-35, byte-identical body |
| `cancel⁻` — Base.lagda.md:62-63 | `extraction.cancel⁻` — Extraction.lagda.md:37-38, byte-identical body |
| `covar` — Base.lagda.md:65-66 | `framing⁺.covar` — Framing.lagda.md:99-100 |
| `coact` — Base.lagda.md:68-69 | `framing⁻.coact` — Framing.lagda.md:53-54 |
| `act-π` — Base.lagda.md:71-72 | `framing⁺.act-π` — Framing.lagda.md:102-103 |
| `act` — Base.lagda.md:74-75 | `framing⁺.act` — Framing.lagda.md:105-106 |
| `composite⁺` — Base.lagda.md:77-78 | `framing⁻.composite⁺` — Framing.lagda.md:77-78 (via `inj⁺`, definitionally equal) |
| `composite⁻` — Base.lagda.md:80-81 | `framing⁺.composite⁻` — Framing.lagda.md:117-118 (via `inj⁻`, definitionally equal) |
| `representable` — Base.lagda.md:83-84 | `is-representable` — Stability.lagda.md:32-33 |
| `stable` (field) — Base.lagda.md:87 | `is-stable` — Stability.lagda.md:62-63 |
| `cut⁺` (field) — Base.lagda.md:88-89 | `is-composable⁺` — Framing.lagda.md:80-82 |
| `cut⁻` (field) — Base.lagda.md:90-91 | `is-composable⁻` — Framing.lagda.md:120-122 |
| `extracted.reflect-lc` — Base.lagda.md:103-104 | `reflect-lc` — Stability.lagda.md:69-70, same proof shape |
| `extracted._⨾⁺_` — Base.lagda.md:106-107 | `tower⁺._⨾⁺_` — Tower.lagda.md:39-40 |
| `extracted.reflect-⨾⁺` — Base.lagda.md:109-111 | `tower⁺.reflect-⨾⁺` — Tower.lagda.md:42-44 |
| `extracted.absorb⁻` — Base.lagda.md:113-114 | `extraction.absorb⁻` — Extraction.lagda.md:47-48, byte-identical body |
| `extracted.composite-twist⁺` — Base.lagda.md:116-117 | `extraction.theory.composite-twist⁺` — Extraction.lagda.md:58-60, byte-identical body |
| `extracted.unitr⁺` — Base.lagda.md:119-121 | `extraction.theory.unitr⁺` — Extraction.lagda.md:62-64, same proof shape |

No gaps.

## `src/Bb/OneTwist/Cancel.lagda.md`

**Verdict: FULLY VENDORED** (both the general `system⁻` part and the
Klein-four countermodel).

### `module system⁻` (the general `⁺`-tier theory)

| `OneTwist.Cancel` (`file:line`) | `VirtualGraphs.Degenerate.Extraction` (`file:line`) |
| --- | --- |
| `centre⁺` — Cancel.lagda.md:56-57 | `system⁻.centre⁺` — Extraction.lagda.md:82-83, byte-identical |
| `centre-cancel⁺` — Cancel.lagda.md:59-60 | `system⁻.centre-cancel⁺` — Extraction.lagda.md:85-86, byte-identical |
| `absorb⁺` — Cancel.lagda.md:62-63 | `system⁻.absorb⁺` — Extraction.lagda.md:88-89, byte-identical |
| `_⨾⁻_` — Cancel.lagda.md:65-66 | `tower⁻._⨾⁻_` — Tower.lagda.md:82-83 |
| `reflect-⨾⁻` — Cancel.lagda.md:68-70 | `tower⁻.reflect-⨾⁻` — Tower.lagda.md:85-87 |
| `composite-centre⁺` — Cancel.lagda.md:72-73 | `system⁻.composite-centre⁺` — Extraction.lagda.md:91-93, byte-identical |
| `unitl⁻` — Cancel.lagda.md:75-77 | `system⁻.unitl⁻` — Extraction.lagda.md:95-97, same proof shape |
| `cancel⁺` — Cancel.lagda.md:86-87 | `system⁻.cancel⁺` — Extraction.lagda.md:99-100, byte-identical |
| `agree` — Cancel.lagda.md:89-90 | `system⁻.agree` — Extraction.lagda.md:102-103, byte-identical |
| `cancel⁺→agree` — Cancel.lagda.md:92-93 | `system⁻.cancel⁺→agree` — Extraction.lagda.md:105-106, byte-identical |
| `agree→cancel⁺` — Cancel.lagda.md:95-96 | `system⁻.agree→cancel⁺` — Extraction.lagda.md:108-110, byte-identical |

### The Klein-four countermodel

| `OneTwist.Cancel` (`file:line`) | `VirtualGraphs.Bool.Klein` (`file:line`) |
| --- | --- |
| `K`, `_⊕_`, `0₄ v⁻ v⁺ c⁺`, `σ ψ`, `σψ`, `ψσ`, `σ-inj`, `⊕-assoc`, `⊕-invol`, `⊕-unitr`, `⊕-comm`, `⊕-cancel-l`, `⊕-cancel-r`, `K-set` — Cancel.lagda.md:105-165 | Same names, byte-identical bodies — Klein.lagda.md:43-102 |
| `cπ`, `aπ`, `rf`, `cπ-inj`, `aπ-inj`, `rf-inj`, `tier⁻`, `tier⁺` — Cancel.lagda.md:175-207 | Same names, byte-identical bodies — Klein.lagda.md:118-150 |
| `model` (graph⁻ instance, bundled fields) — Cancel.lagda.md:209-226 | `KM` (minimal `ob`/`hom`/`reflect`) plus separately named `S`, `cut⁺`, `cut⁻` — Klein.lagda.md:113-116, 152-167. `stable` field's body is restated through the general helper `stable-from-injective`; `cut⁺`/`cut⁻` bodies are byte-identical |
| `is-true`, `no-agree`, `no-cancel⁺` — Cancel.lagda.md:239-247 | Byte-identical — Klein.lagda.md:179-188 |
| `⨾⁻twist⁺-cancellable` — Cancel.lagda.md:258-261 | Klein.lagda.md:197-200, identical up to substituting the extracted `twist⁺ tt` for its computed value `v⁺` |
| `no-frame⁻` — Cancel.lagda.md:263-264 | Klein.lagda.md:202-203, same substitution |

No gaps.

## `src/Bb/OneTwist/Models.lagda.md`

**Verdict: FULLY VENDORED** (both the path-groupoid model and the
abelian-group model).

### `module path-model` → `Groupoid.Path`, `module one-twist`

`Groupoid/Path.lagda.md` splits the OneTwist path-model in two: a
general two-twist `module path` (general theory, attributed by the
CHANGELOG to `Bb.WeakDeductiveSystem.Gist.FramedCut`, not to
`OneTwist`) and a `module one-twist` built on top of it that is the
actual one-twist instance.

| `OneTwist.Models` (`file:line`) | `VirtualGraphs.Groupoid.Path` (`file:line`) |
| --- | --- |
| `emb`, `emb-equiv` — Models.lagda.md:46-50 | Byte-identical, inside `module path` — Path.lagda.md:41-45 |
| `Tm`, `Cot` — Models.lagda.md:52-56 | Subsumed by the general `virtual-graph.term`/`coterm`, opened at Path.lagda.md:53 |
| `Rf` — Models.lagda.md:58-59 | `virtual-graph.reflect` field of `PG` — Path.lagda.md:50-51, byte-identical body |
| `term-contr` — Models.lagda.md:61-63 | Byte-identical — Path.lagda.md:56-58 |
| `coterm-contr` — Models.lagda.md:65-67 | Byte-identical — Path.lagda.md:60-62 |
| `recentre` — Models.lagda.md:69-71 | Byte-identical — Path.lagda.md:64-66 |
| `curry≃` — Models.lagda.md:73-79 | Same body (target type folded into `judgment`) — Path.lagda.md:68-72 |
| `Rf-equiv` — Models.lagda.md:81-82 | `reflect-equiv` — Path.lagda.md:74-75, byte-identical |
| `slot≃` — Models.lagda.md:84-88 | Byte-identical — Path.lagda.md:77-80 |
| `slot-swap≃` — Models.lagda.md:90-94 | Byte-identical — Path.lagda.md:82-85 |
| `cπ-equiv` — Models.lagda.md:96-100 | `coact-π-equiv` — Path.lagda.md:87-91, identical up to `var x` unfolding to `(x, t⁻ x)` |
| `C⁺` — Models.lagda.md:107-110 | Subsumed by the general `composite⁺` (`framing⁻.composite⁺`, Framing.lagda.md:77-78) applied to `PG` |
| `τ⁺` — Models.lagda.md:112-113 | `extraction.twist⁺`, opened in `module one-twist` — Path.lagda.md:255 |
| `C⁻` — Models.lagda.md:115-118 | Subsumed by the general `composite⁻` (`framing⁺.composite⁻`, Framing.lagda.md:117-118) |
| `PG` (bundled graph⁻ instance) — Models.lagda.md:120-128 | Split: `PG` (`ob`/`hom`/`reflect` only) at Path.lagda.md:47-51, plus `U⁻`, `S`, `C⁺`, `C⁻` named separately in `module one-twist` — Path.lagda.md:252-264, byte-identical bodies |
| `aπ-equiv` — Models.lagda.md:130-134 | `one-twist.act-π-equiv` — Path.lagda.md:266-270, identical up to `τ⁺`/`twist⁺` naming |
| `PG-invertible⁺` — Models.lagda.md:136-137 | `one-twist.U⁺` — Path.lagda.md:272-273, byte-identical |
| `open system⁻ PG PG-invertible⁺ using (unitl⁻; cancel⁺; agree)` — Models.lagda.md:139 | `open extraction.system⁻ PG t⁻ U⁻ S C⁺ C⁻ U⁺ using (unitl⁻; cancel⁺; agree)` — Path.lagda.md:275-276, same exports |

No gaps.

### `module group-model` → `Group.Abelian`, `module one-twist`

`Group/Abelian.lagda.md` hypothesizes the group once in an outer
`module _`, then opens a `module one-twist (t⁻ : A)` for the
one-twist instance.

| `OneTwist.Models` (`file:line`) | `VirtualGraphs.Group.Abelian` (`file:line`) |
| --- | --- |
| `unitr` — Models.lagda.md:158-159 | Byte-identical — Group/Abelian.lagda.md:50-51 |
| `invr` — Models.lagda.md:161-162 | Byte-identical — Group/Abelian.lagda.md:53-54 |
| `inv-invol` — Models.lagda.md:164-175 (with a locally-scoped `cancel-r`) | `one-twist.inv-invol` — Group/Abelian.lagda.md:446-447, same statement, reusing the outer module's already-defined `cancel-r` instead of a local copy |
| `cancel-l` — Models.lagda.md:177-185 | Byte-identical (renamed bound variables) — Group/Abelian.lagda.md:56-64 |
| `cancel-r` — Models.lagda.md:187-188 | Byte-identical — Group/Abelian.lagda.md:66-67 |
| `cπ`, `aπ`, `gf`, `cπ-inj`, `aπ-inj`, `gf-inj`, `absorb-wit`, `tier⁻`, `tier⁺` — Models.lagda.md:190-221 | Byte-identical, inside `module one-twist` — Group/Abelian.lagda.md:371-402 |
| `GM` (bundled graph⁻ instance) — Models.lagda.md:223-236 | Split: `GM` (`ob`/`hom`/`reflect` only) plus named `S`, `cut⁺`, `cut⁻` — Group/Abelian.lagda.md:404-420, byte-identical bodies |
| `GM-invertible⁺` — Models.lagda.md:238-239 | Passed inline as `(λ _ → tier⁺)` to `extraction.system⁻` — Group/Abelian.lagda.md:430 |
| `open system⁻ GM GM-invertible⁺ using (agree; cancel⁺; agree→cancel⁺)` — Models.lagda.md:241 | `open extraction.system⁻ GM (λ _ → t⁻) (λ _ → tier⁻) S cut⁺ cut⁻ (λ _ → tier⁺)` — Group/Abelian.lagda.md:430 (unrestricted open, superset of the OneTwist export list) |
| `twist⁺-forced` — Models.lagda.md:249-251 | Byte-identical — Group/Abelian.lagda.md:437-439 |
| `group-agree` — Models.lagda.md:259-260 | Byte-identical — Group/Abelian.lagda.md:449-450 |
| `group-cancel⁺` — Models.lagda.md:262-263 | Byte-identical — Group/Abelian.lagda.md:452-453 |

No gaps.

## Live-dependency check

```
rg -n "open import Bb\.OneTwist|import Bb\.OneTwist" --type agda src/ 2>/dev/null | grep -v "^src/Bb/OneTwist/"
```

Output: empty (no matches outside `src/Bb/OneTwist/` itself).

## `src/Bb/index.lagda.md`

Still imports all three `OneTwist` modules:

```
138:import Bb.OneTwist.Base
139:import Bb.OneTwist.Cancel
140:import Bb.OneTwist.Models
```

This is the standard `Bb` archive-index entry (`src/Bb/CLAUDE.md`:
"`src/Bb/index.lagda.md` imports every module of every subfolder"),
present for every frozen `Bb` tree regardless of whether a later tree
restates its content — not evidence of a live dependency. No other
module in `src/` imports `Bb.OneTwist.*` (per the `rg` check above).

## Summary verdict

**Safe to retire in full.** Every named definition, record field, and
theorem across `Bb.OneTwist.Base`, `Bb.OneTwist.Cancel`, and
`Bb.OneTwist.Models` has a corresponding definition in
`Bb.VirtualGraphs` — most bodies byte-identical, the rest equivalent
restatements via the tree's shared flat-parameter vocabulary
(`Type`/`Stability`/`Framing`/`Tower`) instead of `OneTwist`'s bundled
record. No gaps found in any of the three source files. No code
outside `src/Bb/OneTwist/` imports it. `Bb.index` still lists the
tree, per the standing archive-index convention, not as a sign of a
live dependency.
