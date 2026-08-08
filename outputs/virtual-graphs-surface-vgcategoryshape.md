# Surface audit: `Bb.VgCategoryShape` → `Bb.VirtualGraphs`

Content-level check of whether everything named or proved in
`src/Bb/VgCategoryShape/` is actually present, verbatim or as an
equivalent restatement, in the destination modules the
`Bb.VirtualGraphs` `CHANGELOG.md` cites for it.

## File inventory

`find src/Bb/VgCategoryShape -type f`:

```
src/Bb/VgCategoryShape/Base.lagda.md
src/Bb/VgCategoryShape/CHANGELOG.md
src/Bb/VgCategoryShape/Parity.lagda.md
src/Bb/VgCategoryShape/README.md
src/Bb/VgCategoryShape/Type.lagda.md
src/Bb/VgCategoryShape/Unit.lagda.md
```

Four `.lagda.md` modules carry mathematical content: `Type`, `Base`,
`Unit`, `Parity`. `README.md` and `CHANGELOG.md` are process
documents. There is no `Mag.*` subtree in this directory — the
`Mag` name appears only in `README.md` prose, as the name of a
still-unstarted successor project at `src/Mag` (does not exist;
confirmed below).

Per the `Bb.VirtualGraphs` `CHANGELOG.md` (2026-08-04, "interchange,
the extraction, and the aligned edge" entry): `Bb.VirtualGraphs.Aligned`
is "group V, from `Bb.VgCategoryShape` entire minus its model," and
`Bb.VirtualGraphs.Bool.Heap` is `Bb.VgCategoryShape.Parity`, "run
through `Aligned` at each origin." In practice the non-model content
is split across four destination modules — `Type`, `Stability`,
`Framing`, `Interchange` — with `Aligned` as the top of that stack;
this matches the tree-wide flat-parameter design stated in
`Bb.VirtualGraphs.README.md`'s Relationships section ("the extra data
enters as explicit module parameters instead").

---

## `src/Bb/VgCategoryShape/Type.lagda.md`

**Verdict: FULLY VENDORED** (restructured — one record split into a
bare carrier plus explicit framing/interchange parameters).

| Source (`Type.lagda.md`) | Destination |
| --- | --- |
| `hcategory` record: `ob`, `hom`, `term`, `coterm`, `argument`, `conclusion`, `judgment`, `reflect` (:29–51) | `Bb.VirtualGraphs.Type` `virtual-graph`: `ob`, `hom`, `term`, `coterm`, `argument`, `conclusion`, `judgment`, `reflect` (Type.lagda.md:21–43) |
| `representable` (:56–57) | `is-representable`, `Bb.VirtualGraphs.Stability`:32–33 (renamed) |
| `is-stable`, `is-stable-is-prop` (:59–64) | `Bb.VirtualGraphs.Stability`:62–67 |
| `is-neutral`, `is-neutral-is-prop` (:74–82) | `Bb.VirtualGraphs.Aligned`:48–56 |
| `rx` field, `var`, `covar`, `axiom`, `eval` (:92–105) | Split into `twist⁻`/`twist⁺` parameters: `Bb.VirtualGraphs.Framing` `framing⁻.var`:47–48, `framing⁺.covar`:99–100, `framing.axiom`/`eval`:139–144. `Aligned` instantiates both twists to one `rx` (`open framing G rx rx`, Aligned.lagda.md:64) |
| `readback` field (:107–108) | `readback-of`, `Bb.VirtualGraphs.Framing`:153–154, taken as parameter `R` in `Aligned` |
| `coact-π`, `coact`, `act-π`, `act` (:114–124) | `Framing`'s `framing⁻.coact-π`/`coact`:50–54, `framing⁺.act-π`/`act`:102–106 |
| `composite⁺`, `composite⁻`, `cut⁺`, `cut⁻` fields, `_⨾⁺_`, `_⨾⁻_`, `reflect-⨾⁺`, `reflect-⨾⁻` (:135–159) | `composite⁺`/`composite⁻` in `Framing`'s `framing⁻`/`framing⁺` (via `inj⁺`/`inj⁻`); `_⨾⁺_`, `_⨾⁻_`, `reflect-⨾⁺`, `reflect-⨾⁻` in `Bb.VirtualGraphs.Degenerate.Interchange`'s `framed-interchange`:64–76 (cut fields become parameters `cc⁺`, `cc⁻`) |
| `unital`, `is-unital` (:173–177) | `Bb.VirtualGraphs.Aligned`:106–110, verbatim |
| `unit` field, `idn`, `idn-neutral`, `idn-idem⁻` (:179–189) | `Aligned`'s `pinned` module:118–125 (`unit` becomes a module parameter instead of a record field) |

No gaps. Every field and derived definition has a destination; the
transformation is the stated one (record → flat parameters), not a
content loss.

---

## `src/Bb/VgCategoryShape/Base.lagda.md`

**Verdict: FULLY VENDORED.**

All 33 lemmas in the `hcat` module map to `Bb.VirtualGraphs.Degenerate.Interchange`'s
`framed-interchange` module (re-exported `public` by `Aligned.lagda.md:72`,
with `unitr⁺`/`unitl⁻` renamed to `unitr⁺rx`/`unitl⁻rx` on that same
line, matching Base's own names) or directly into `Aligned`'s `pinned`
module:

| Source (`Base.lagda.md`) | Destination |
| --- | --- |
| `reflect-lc` (:36–37) | `Aligned.lagda.md`:80–81 |
| `coact-covar` (:39–40) | `Interchange.lagda.md`:78–79 (via `Aligned` public re-export) |
| `act-var` (:42–43) | `Interchange.lagda.md`:81–82 (public) |
| `unitr⁺rx` (:50–62) | `Interchange.lagda.md` `unitr⁺`:91–96, renamed `unitr⁺rx` at `Aligned.lagda.md`:73 |
| `unitl⁻rx` (:57–62) | `Interchange.lagda.md` `unitl⁻`:98–103, renamed `unitl⁻rx` at `Aligned.lagda.md`:73 |
| `⨾⁻-is-act` (:68–73) | `Interchange.lagda.md`:129–134 (public) |
| `⨾⁺-is-coact` (:75–80) | `Interchange.lagda.md`:136–141 (public) |
| `read⁺` (:86–91) | `Interchange.lagda.md`:143–148 (public) |
| `read⁻` (:93–98) | `Interchange.lagda.md`:150–155 (public) |
| `mixed-assoc` (:100–102) | `Interchange.lagda.md`:157–159 (public) |
| `le-is-coact` (:108–112) | `Aligned.lagda.md`:87–91 |
| `re-is-act` (:114–118) | `Aligned.lagda.md`:93–97 |
| `idn-pre` (:130–133) | `Aligned.lagda.md`:136–139 |
| `idn-⨾⁺-equiv` (:135–137) | `Aligned.lagda.md`:141–143 |
| `unitl⁻` (:139–153) | `Aligned.lagda.md`:145–159 |
| `post-eqv` (:155–159) | `Aligned.lagda.md`:161–165 |
| `rx≡idn` (:161–163) | `Aligned.lagda.md`:167–169 |
| `unitr⁺` (:169–170) | `Aligned.lagda.md`:175–176 |
| `idem⁺` (:172–173) | `Aligned.lagda.md`:178–179 |
| `coact-⨾⁺` (:175–177) | `Aligned.lagda.md`:181–183 |
| `act-⨾⁻` (:179–181) | `Interchange.lagda.md`:182–184 (public) |
| `idn-post` (:183–186) | `Aligned.lagda.md`:185–188 |
| `absorb⁺` (:188–197) | `Aligned.lagda.md`:190–199 |
| `absorb⁻` (:199–208) | `Aligned.lagda.md`:201–210 |
| `unitl⁺` (:210–215) | `Aligned.lagda.md`:212–217 |
| `unitr⁻` (:217–222) | `Aligned.lagda.md`:219–224 |
| `interchange` (:231–235) | `Aligned.lagda.md`:231–235 |
| `judgment-interchange` (:237–242) | `Aligned.lagda.md`:237–242 |
| `composite⁻-idn` (:252–253) | `Aligned.lagda.md`:250–251 |
| `composite⁺-idn` (:255–256) | `Aligned.lagda.md`:253–254 |
| `reflect-image-contr` (:258–261) | `Aligned.lagda.md`:256–259 |
| `stable` (:263–264) | `Aligned.lagda.md`:261–262 |
| `contr-representable` (:266–269) | `Aligned.lagda.md`:264–267 |
| `assoc⁺` (:275–284) | `Aligned.lagda.md`:274–283 |
| `assoc⁻` (:286–295) | `Interchange.lagda.md`:186–195 (public) |

No gaps.

---

## `src/Bb/VgCategoryShape/Unit.lagda.md`

**Verdict: FULLY VENDORED.**

Everything lands inside `Aligned.lagda.md`'s `pinned` module, in the
same order:

| Source (`Unit.lagda.md`) | Destination (`Aligned.lagda.md`) |
| --- | --- |
| `square-equiv→equiv` (private, :44–51) | :294–301 |
| `neutral→pre` (:53–64) | :303–314 |
| `neutral→post` (:66–77) | :316–327 |
| `cancel` (:83–85) | :329–331 |
| `cancel-equiv` (:87–100) | :333–346 |
| `pinned` (private local type, :111–119) | `pinned-at` (:348–357) — renamed to avoid colliding with the outer module's own name `pinned` |
| `pinned-contr` (:114–119) | :352–357 |
| `unit-contr` (:121–124) | :359–363 |
| `is-unital-is-prop` (:127–128) | :365–366 |

No gaps.

---

## `src/Bb/VgCategoryShape/Parity.lagda.md`

**Verdict: PARTIALLY VENDORED — one gap.**

Destination: `Bb.VirtualGraphs.Bool.Heap`. Every definition and
lemma has a matching counterpart except one:

| Source (`Parity.lagda.md`) | Destination (`Bool/Heap.lagda.md`) |
| --- | --- |
| `arg` (private type synonym, :42) | Not named; `virtual-graph.argument HB tt tt` used inline throughout — definitionally the same type, no content loss |
| `emb` (:44–45) | :53–54 |
| `emb-eval` (:53–54) | :56–57 |
| `emb-lc` (:56–60) | :59–63 |
| `emb-is-embedding` (:62–64) | :65–67 |
| `self` (:75–76) | :78–79 |
| `left-neutral` (:78–81) | :81–84 |
| `right-neutral` (:83–88) | :86–91 |
| `cmp` (:97–98) | :105–106 |
| `shape⁺` (:100–106) | :108–114 |
| `shape⁻` (:108–116) | :116–124 |
| `origin-readback` (:118–119) | `rb` (:126–127) — same proof term, retyped against `framing.readback-of` |
| `heap : Bool → hcategory 0ℓ 0ℓ` record (:123–138) | Distributed: `HB` graph part (:48–50), `rb`/`cut⁺`/`cut⁻` fed as parameters into `aligned` (:141–142), `has-unit` fed into `pinned` (:144–147) — same six field values, same order, restructured per the flat-parameter design |
| `every-edge-is-neutral` (per-origin, :151–152) | `every-edge-is-neutral` (:93–94) — origin-independent in the new carrier, since `is-neutral` in `Aligned` needs only the graph, not `rx`; strictly generalizes the source (one function instead of one per origin) |
| `full-interchange` (:154–155) | :151–152 |
| `false≢true` (:164–165) | :164–165 |
| `rival-is-neutral` (:170–171) | :167–168 |
| `rival-not-idempotent` (:173–174) | :170–171 |
| `rival-not-the-unit` (:176–177) | :173–174 |
| `same-reflection` (:183–187) | **No counterpart.** See gap note below. |
| `compositions-differ` (:189–192) | :176–177 |
| `twist` (:205–206) | :187–188 |
| `twist-arg` (:208–210) | :190–192 |
| `twist-emb` (:212–222) | :194–204 (identical case split, all eight clauses `refl`) |
| `reflection-is-equivariant` (:224–228) | :206–210 |
| `twist-moves-the-origin` (:230–233) | :212–213 |

**Gap: `same-reflection`.** `Parity.lagda.md:183–187` proves
`hcategory.reflect (heap false) m γ ≡ hcategory.reflect (heap true) m γ`
by `refl` — a nontrivial-looking fact in that source's design, where
`heap false` and `heap true` are two separately built `hcategory`
records that happen to share a `reflect` field. `Bool/Heap.lagda.md`
has no lemma of this name or shape. The reason is architectural, not
an omission of proof effort: in the destination carrier there is only
one graph, `HB` (`Bool/Heap.lagda.md:47–50`), with one `reflect`
field; the two origins are two different parameterizations of
`aligned` over that one graph (`module at (o : Bool)`, :141–142), not
two different graphs. The fact `same-reflection` recorded is true by
construction in the new design and has no statement left to make —
but this means the identifier and its explicit proof are genuinely
absent, not merely renamed. Flagged as the tree's one content gap.

---

## `src/Bb/VgCategoryShape/README.md`

Not a vendoring target — process/design document, per `src/Bb/CLAUDE.md`'s
three-section README convention (construction, provenance,
relationships). Its "Provenance" and part of "Relationships" describe
already-archived, already-vendored content (the `hcategory`
construction, the structure/property split, what `Parity` shows) and
raise no separate concern.

**However, its "Relationships" section states an open, unresolved
design question — the `Mag` re-founding program — that is not about
already-proved content, and this section is actively cited elsewhere
in the live tree as the program of record:**

- `src/Cat/Logic/TODO.md:10`: "The `Mag` rebuild remains pending; its
  program of record is `src/Bb/VgCategoryShape/README.md`, the
  vendored staging tree."
- `docs/roadmap.md:38`: "...the `Mag` rebuild: `hcategory` without
  interchange as the θ²-collapsed one-twist instance of that record,
  program of record `src/Bb/VgCategoryShape/README.md`."
- `src/Cat/Logic/TODO.md:901`: "First consumer: the `Mag`
  re-founding program in `src/Bb/VgCategoryShape/README.md`, which
  reads `hcategory` as the θ² = id merge of the two magmoids..."
- `src/Cat/Logic/TODO.md:935`: cites the same file for "the lesson of
  the interchange precedent."

`src/Mag` does not exist yet (confirmed: `ls src/Mag` → no such
directory). The README's target — re-deriving `hcategory` as the
balanced layer of `Cat.Logic` at θ² = id, "a re-founding rather than
a record edit" (`README.md:83`) — is stated as gated on open work
("investigation line 5" in `Cat.Logic`'s TODO, per
`docs/roadmap.md:25–39`) and has not happened. This is a live
planning role, structurally the same situation flagged previously for
`src/Cat/Logic/TODO.md` itself: a document that looks like archive
prose but is a load-bearing pointer for other live files.

`src/Bb/VgCategoryShape/CHANGELOG.md` is ordinary process history —
no live citations found, no open content of its own.

---

## Live-dependency check

The task's specified command:

```
rg -n "open import Bb\.VgCategoryShape|import Bb\.VgCategoryShape" --type agda src/ 2>/dev/null | grep -v "^src/Bb/VgCategoryShape/"
```

produces **empty output** — but this is not informative in this repo.
`rg --type-list` shows ripgrep's built-in `agda` type matches only
`*.agda` and `*.lagda`, not `*.lagda.md`, which is this codebase's
actual file extension throughout (confirmed on every file read for
this audit). The `--type agda` filter therefore matches zero files in
`src/` and the empty result is vacuous, not evidence of absence.

Corrected search, matching the real file extensions:

```
rg -n "open import Bb\.VgCategoryShape|import Bb\.VgCategoryShape" -g '*.lagda.md' -g '*.agda' src/ | grep -v "^src/Bb/VgCategoryShape/"
```

Output:

```
src/Bb/index.lagda.md:153:import Bb.VgCategoryShape.Base
src/Bb/index.lagda.md:154:import Bb.VgCategoryShape.Parity
src/Bb/index.lagda.md:155:import Bb.VgCategoryShape.Type
src/Bb/index.lagda.md:156:import Bb.VgCategoryShape.Unit
```

Exactly one dependent, `src/Bb/index.lagda.md`, importing all four
modules. This is the `Bb`-namespace archive aggregator required by
`src/Bb/CLAUDE.md` ("One index over the namespace... imports every
module of every subfolder") — not a consumer of the theory. No module
under `src/Cat`, `src/Core`, `src/Data`, `src/HData`, `src/Lib`, or
`src/Test` references `Bb.VgCategoryShape` at all.

## `src/Bb/index.lagda.md` check

Still imports all four modules, at lines 153–156 (shown above). Any
retirement of the tree's `.lagda.md` modules requires removing these
four import lines as part of the same change.

---

## Summary verdict

**Retire with named exceptions — not a full retirement.**

- The proved mathematical content of `Type.lagda.md`, `Base.lagda.md`,
  and `Unit.lagda.md` is **fully vendored**, verbatim in substance,
  into `Bb.VirtualGraphs.{Type,Stability,Framing,Interchange,Aligned}`.
- `Parity.lagda.md` is **vendored with one exact gap**:
  `same-reflection` (`src/Bb/VgCategoryShape/Parity.lagda.md:183–187`)
  has no counterpart in `src/Bb/VirtualGraphs/Bool/Heap.lagda.md`. The
  fact it recorded is now true by construction rather than proved, but
  the named lemma is absent.
- Zero live code outside the archive index depends on the tree
  (confirmed by a corrected search; the task's specified `rg --type
  agda` command is vacuous in this repo and must not be read as
  evidence on its own).
- **Premature to retire in full.** `src/Bb/VgCategoryShape/README.md`
  is cited as the "program of record" for the still-open, still-gated
  `Mag` re-founding project in `src/Cat/Logic/TODO.md:10,901,935` and
  `docs/roadmap.md:38`. That content is a forward-looking design
  question, not archived proof, and deleting the README (or the
  directory it lives in) without first repointing those four
  citations would orphan live planning documents — the same failure
  mode previously found for `src/Cat/Logic/TODO.md` itself.

If the tree is retired: the four `.lagda.md` modules and
`CHANGELOG.md` can go once the `same-reflection` gap is either
accepted or closed in `Bool/Heap.lagda.md`, and the four `Bb.index`
import lines are removed. `README.md` must either stay in place, or
be relocated with `src/Cat/Logic/TODO.md:10,901,935` and
`docs/roadmap.md:38` repointed to its new location, before the
directory disappears.
