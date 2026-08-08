# Bb.VirtualGraphs — redundancy and thematic organization

Survey of the 55 code modules: 14 mainline beside `Type`, 17 under
`Degenerate`, 24 models under `Bool`, `Circle`, `Word`, `Group`, and
`Groupoid`.

Size is not the problem. Only `Tower` (319 code lines) passes 300 in
the mainline. Four model modules pass it: `Word/Defect` (399),
`Bool/Sleeve` (369), `Groupoid/Engine` (341), `Word/Census` (330).
Every other module has room. The problem is that the same content
occupies several modules at once.

## 1. The diagonal stack

Four mainline modules take one family of endo-edges and let it fill
both argument slots.

| Module | Parameter |
| --- | --- |
| `Engine` | `idn : (x : ob) → hom x x` |
| `Lens` | `idn`, through `Engine.chosen` |
| `Stable` | `idn`, through `Engine.chosen` |
| `Displaced` | `idn`, through `Engine.chosen` |

`Curried` does the same over its own carrier. Its `rx` fills both far
slots of `emb`, and it imports nothing from the tree.

Setting `rx = corx` identifies the two half-twist families. Under the
criterion that `Degenerate` holds degenerating constructions, these
five modules belong there. The import graph makes the block clean:
the diagonal stack reaches the two-family stack only through
`Engine → Graph`, and only for `rxgraph`.

Five `Degenerate` modules already sit downstream of `Engine`:
`CrossedUnit`, `Engine`, `Lens`, `Reflexive`, `UnitShape`. They would
stop crossing a namespace boundary to reach their own base.

What stays in the mainline is the two-family theory: `Type`,
`Embedding`, `Framing`, `Graph`, `Tower`, `Twist`, `Recognition`,
`Mediation`, `Pentagon`, `Polarity`. Ten modules.

## 2. The diagonal stack restates the framing vocabulary

`Engine.chosen` is `framing G idn idn`, term for term. Each pair
below agrees by `refl`.

| `Engine.chosen` | `Framing` at the diagonal |
| --- | --- |
| `var`, `covar`, `eval` | `framing.var`, `covar`, `eval` |
| `coact-π`, `coact` | `framing⁻.coact-π`, `coact` |
| `act-π`, `act` | `framing⁺.act-π`, `act` |
| `composite⁻` | `framing⁻.composite⁺` |
| `composite⁺` | `framing⁺.composite⁻` |

The composition register is crossed. `Engine`'s prose states the
crossing at line 3, and `Framing`'s prose states it at line 13. The
name `composite⁻` still denotes two different operations in two
modules of one tree. `Lens.inj⁻` and `framing⁻.inj⁺` carry the same
crossing.

Two more pairs agree the same way:

- `Engine.dict.graph` is `Graph.graphs.graph⁺`, and also `graph⁻`.
  `dict`'s six dictionary entries restate `graphs`'s five.
- `Lens.lens.two-sided`, `bipush`, and `judgment-fam` restate
  `Graph.two-sided.base`, `bipush`, and `judgment-fam`.

The fix is to define the diagonal dialect as the instance it is,
rather than to copy it. That removes the copies and the crossed name
at once.

## 3. Readback is stated four times

One type, four names, four modules.

| Name | Module |
| --- | --- |
| `framing.readback-of` | `Framing:134` |
| `lens.readback` | `Lens:53` |
| `readback` | `Stable:65` |
| `candidate.rb` | `Recognition:62` |

`Degenerate/Readback` names a fifth scope over the same idea.

## 4. The mediation clauses are stated three times

`Recognition.clause.clause₀`/`clause₁` state the clauses over
judgments. `Recognition.at-framing.law₀`/`law₁` state them over
edges at the carrier's framing. `Mediation.mediation.clause₀`/
`clause₁` state them over edges at a candidate pair.

`law₀ x` is `clause₀ x (rx x , corx x)`, and `law₁ x` is
`clause₁ x (rx x , corx x)`. `at-framing.lead₁` is
`mediation.corr₁` at the same pair.

The two modules take identical parameter lists, `(G) (rx corx) (S)
(C⁺) (C⁻)`, and both open `tower` publicly. `Recognition` and
`Mediation` are one development split across two files.

`Mediation.self.framed` and `framed-is-prop` repeat
`Mediation.mediation.framed` and `framed-is-prop` verbatim. Only the
mediation predicate differs.

## 5. Degenerate repeats one absorption lemma four times

`absorb⁻` and `absorb⁺` appear with identical statements and
identical proof terms in four modules.

```agda
absorb⁻ : ∀ {y} (k : coterm y) → coact (corx y) k ≡ k
absorb⁻ {y} k i = k .fst , cancel⁻ y i k
```

`Cancellation:66`, `Display:48`, `Neutral:151`, and `Extraction:49`
carry that text. `Degenerate/Tower:40` states the same type from
`pin⁻ ∙ K⁻` instead. The lemma takes `cancel⁻` and returns the
coterm form. It wants one home.

The unit laws spread the same way. `unitr⁺ : f ⨾⁺ corx y ≡ f` and
`unitl⁻ : rx x ⨾⁻ g ≡ g` appear in `Degenerate/Tower`,
`Extraction`, `Interchange`, and `Readback`.

## 6. One unit-law name, two statements

`unitl⁺` means `corx w ⨾⁺ s ≡ s` in `Cancellation:90` and
`rx x ⨾⁺ g ≡ g` in `Interchange:271`. The two statements put a
different family in the unit position. `Interchange` also states both
polarity pairs itself, at lines 92 and 99 and again at 271 and 274.

## 7. Dictionaries of refl

155 declarations across 30 modules are proved by `refl` alone. The
densest are the dictionary modules.

| Module | refl proofs / declarations |
| --- | --- |
| `Bool/Readers` | 20 / 48 |
| `Word/Defect` | 18 / 83 |
| `Word/Carrier` | 17 / 55 |
| `Engine` | 15 / 43 |
| `Graph` | 9 / 15 |

`docs/guidelines/definitions-and-proofs.md:63` already rules on this:
a candidate that holds definitionally "earns no lemma at all: use
sites write the definitional form." The rule sits inside the
paragraph on Core additions, so the archive reads as exempt.

`Engine:132` states the practice as a result: "Every proof is `refl`,
so each answer is a definitional equality: the two languages describe
one object." That sentence is the reason the module exists. Once the
diagonal dialect instantiates the framing rather than restating it,
the two languages are one expression and the dictionary has nothing
left to say.

## 8. Duality sits in seven modules

| Module | Content |
| --- | --- |
| `Embedding` | `opⱽ`, `opⱽ-invol`, `op-embedding` |
| `Graph` | `op-rxgraph` |
| `Engine` | `swap-arg`, `swap-judgment`, `reflect-op`, `composite-op` |
| `Framing.duality` | `op-eval`, `op-readback`, `op-composable` |
| `Tower.op-tower` | `op-⨾⁺`, `op-assoc⁺` |
| `Stable` | `swap-judgment⁻`, `rep-op`, `composable-op`, `unital-op` |
| `Degenerate/Absorb.duality⁰` | `op-absorbing⁻`, `op-absorbing⁺` |

`Engine.swap-judgment` and `Stable.swap-judgment⁻` are the two
directions of one equivalence, held in two modules. `Stable` builds
`swap-eqv` from both.

The swap of arguments is two-family content that does not read `idn`
at all. It can leave the diagonal stack and join `Embedding`.

## 9. Naturality sits in three modules

`Framing:165-246` states `is-natural⁻`, `is-natural⁺`, the six
pairings `own`/`alt`/`mixed`, the diagonal reading, and the two
judgment forms. `Tower:401` and the 135 lines under it prove the
transfer between those forms. `Twist` states `θ-nat` for the twist.

`Framing`'s notion reads one half-twist in one slot. `Twist`'s reads
one half-twist in each of two slots. The arity is the distinction
that decides collapse, and the two notions currently share the word
"naturality" across three files without a statement of how they
differ.

## 10. One layering inversion

`Degenerate/UnitShape` imports `Groupoid.Path`, a model. No other
theory module imports a model.

## What landed

The tree's `CHANGELOG.md` carries the entry. Every item above was
acted on, with two departures.

`Recognition` and `Mediation` did not merge. Each has a model
counterpart under `Word`, `Circle`, or both, so a merge would leave
four model modules named for a theory module that no longer exists.
The duplication went instead: `at-framing.law₀` and `law₁` are now
`mediation.clause₀` and `clause₁` read at the framing's own candidate
pair.

The naturality transfer did not join `Framing`. `Framing` sits below
`Tower` and the transfer needs the tower, so a new `Naturality`
module took the transfer alone. `Framing` keeps the two tier
statements, which read the framing and nothing else.

Counts after: eleven theory modules, twenty-one under `Degenerate`,
twenty-three models. Every theory module is inside the 300-line
budget. `Tower` fell from 319 to 221.
