---
artifact: escardo-typetopology.tar.gz
sha256: 9a6b6adb1eeba27a22eae433e07e62d7586b3fca0073f4ff9c4f97528a306306
format: source-tree
fetch-url: https://github.com/martinescardo/TypeTopology.git
metadata-url: https://github.com/martinescardo/TypeTopology
version: f84d5fa59beece81fb7211957c3e58cb6ba6f65e
fetched: 2026-08-10
sha256-inner: 7702abaa88ee146b5e18258ba6440a1f1adb2cd4a6e56fddea56b854abedbd7b
---

# Escardó and contributors - TypeTopology

An actively evolving Agda development of constructive univalent
mathematics. The project describes itself as a research blackboard for
new mathematics rather than an encyclopedia, with a foundation in a
minimal intensional Martin-Löf type theory and explicit assumptions for
principles from HoTT/univalent foundations or classical mathematics.

Load declaration: canonical-authority corpus. Mathematical use is
resolved at the individual source-file level, where TypeTopology records
authors, contribution dates, and research context. This entry supplies
repository-level custody and navigation; it deliberately does not erase
that finer provenance into anonymous corpus-wide theorem digests.

## Citation

Martín H. Escardó and contributors. *TypeTopology*. Agda development.
GitHub repository `martinescardo/TypeTopology`, commit
`f84d5fa59beece81fb7211957c3e58cb6ba6f65e` (10 August 2026).
<https://github.com/martinescardo/TypeTopology>. GNU General Public
License, version 3. No DOI.

This follows the repository's requested citation: title
`TypeTopology`, author "Escardó, Martín H. and contributors", URL, and
the note "Agda development" (`snapshot/README.md:39-53`). The commit pin
is added here to identify the exact evolving snapshot.

## Vetting and authority

Ingested 2026-08-10 at Lane's direction. The repository's own README,
safe and all-modules indices, library flags, build file, license,
contribution guidance, and AI policy were opened. GitHub's live
`master` reference and an independent remote query both identified
`f84d5fa59beece81fb7211957c3e58cb6ba6f65e`; the shallow checkout has
that commit as `HEAD`. The canonical archive was generated twice from
that checkout and the two outputs were byte-identical.

**Authority directive (Lane, 2026-08-10): this pinned TypeTopology
snapshot is a canonical authority on the subjects it presents. It does
not require an independent statement audit before it may bear load.**
This is an explicit exception to the ordinary resource-entry audit
gate. It does not turn every module into a claim about every subject:
authority remains scoped to what the cited file actually defines,
states, or proves.

Vetted: 2026-08-10, Lane (explicit canonical-authority designation;
independent statement verification waived for this entry).

The development was not type-checked during ingestion. The source says
the snapshot is tested with Agda 2.8.0 (`snapshot/source/index.lagda:14`),
and its Makefile also names Agda 2.8.0 as the latest released target and
2.9.0 as supported/development (`snapshot/Makefile:1-18`). Those are
source claims preserved here, not a fresh build report.

## Mandatory downstream attribution

**Any use of material from this entry in a formal artifact, informal
artifact, or conversation that departs from TypeTopology's findings
must carry detailed authorship and research-provenance citation.** This
condition applies to definitions, theorem statements, proofs, proof
ideas, constructions, examples, counterexamples, computations, design
choices, and organizational findings.

A compliant use records all of the following:

1. The corpus citation above and pinned commit
   `f84d5fa59beece81fb7211957c3e58cb6ba6f65e`.
2. The exact vendored source path and line anchor(s), under `snapshot/`.
3. Every author or contributor named in that file's preamble or next to
   the material used, together with the recorded contribution date(s).
4. The research provenance stated by the file: associated paper,
   antecedent result, collaborator attribution, historical note, or
   source citation, whenever present.
5. A distinction between a checked Agda declaration, explanatory
   prose, an assumption, an unsafe module, and a conjectural or
   work-in-progress remark whenever that distinction affects the use.

The generic repository citation "Escardo and contributors" is
necessary but not sufficient for result-level use when the source file
provides more precise authorship. If a file's authorship or research
provenance cannot be resolved, the material must not be exported as an
attributed finding until the ambiguity is resolved. In conversation, a
compact citation is acceptable only if it still names the author(s),
file and line, contribution date or provenance note, and commit.

This requirement follows the corpus's own authorship practice: the root
README asks contributors to add their full name and date at the place of
contribution (`snapshot/README.md:5-9`), and the contribution guide
requires visible author/date records for each contribution
(`snapshot/CONTRIBUTING.md:37-45`).

## Files

Canonical format: **repository source tree** (`source-tree`). All
vendored forms are gitignored; only this README is tracked.

- `escardo-typetopology.tar.gz` - canonical artifact, produced by
  `git archive` from the pinned commit. It contains all 1,052 tracked
  files and no `.git` metadata. The frontmatter `sha256` identifies this
  file; `sha256-inner` identifies its decompressed tar stream.
- `snapshot/` - complete extraction of the canonical artifact for
  grepping. Files are byte-identical to their archive members.
- `snapshot/source/` - the formal development: 990 `.agda` and
  `.lagda` files, 287,827 lines including prose, comments, and blanks.
- `snapshot/source/index.lagda` - safe-module root and repository
  philosophy. It imports each safe development through its local
  `index.lagda` (`snapshot/source/index.lagda:140-208`).
- `snapshot/source/AllModulesIndex.lagda` - imports the safe root plus
  `Unsafe.index` and `InfinitePigeon.index`; its header explains the
  distinct checking status (`snapshot/source/AllModulesIndex.lagda:16-48`).
- `snapshot/typetopology.agda-lib` - authoritative global Agda flags.
- `snapshot/Makefile` - whole-development checking targets.
- `snapshot/README.md` - project description, requested citation,
  publication list, and contributor list.
- `snapshot/LICENSE` - GNU GPL version 3 text.
- `snapshot/AI-Policy.md` - the repository's one-line policy that it
  will not consider AI-generated pull requests. Vendoring and citing
  the repository does not propose an upstream contribution.

Jump with `sed -n 'A,Bp' snapshot/<path>` from this directory. For a
mathematical result, begin at its directory's `index.lagda`, then cite
the defining module rather than the index alone.

## Source provenance

Obtained from the public, non-fork GitHub repository on 2026-08-10.
The frontmatter `fetch-url` names the repository and `version` pins the
immutable commit that was the `master` head at ingestion. The pinned
commit was authored and committed by Martin Escardo on 2026-08-10 with
the message `typo`. The repository has no submodules.

GitHub's generated download archives are not used as the canonical byte
identity. The canonical tarball was instead generated locally and
deterministically from the pinned Git object with `git archive`; two
independent archive runs matched byte-for-byte. A future `master` head
will be a different source vintage and must be ingested under a new
commit pin and hashes rather than silently replacing this artifact.

## Section map

This is a corpus-level navigation map. Result-level citation must
continue into the indicated subtree's own index and then the defining
module, under the mandatory attribution rule above.

- `snapshot/README.md:1-13` - title, history since approximately 2010,
  and rendered/searchable interfaces.
- `snapshot/README.md:29-37` - self-description as a research
  blackboard; `snapshot/README.md:39-53` - requested citation;
  `snapshot/README.md:55-60` - safe/all-module roots and local indices.
- `snapshot/README.md:62-308` - publications and preprints resulting
  from the development; `snapshot/README.md:309-354` - contributors.
- `snapshot/source/index.lagda:1-69` - identity, supported Agda vintage,
  working character, explicit-assumption discipline, and corpus size.
- `snapshot/source/index.lagda:71-139` - foundational philosophy:
  univalent point of view, Spartan MLTT, safety flags, explicit axioms,
  constructive/classical boundaries, and avoidance of Cubical Agda.
- `snapshot/source/index.lagda:140-160` - first safe imports: apartness,
  algebraic structures, binary systems, Cantor-Schroeder-Bernstein,
  cardinals, categories, conaturals, continuity, coslices, crossed
  modules, C-spaces, Dedekind reals, and discrete graphic monoids.
- `snapshot/source/index.lagda:161-180` - domain theory, dominances,
  duploids, dyadics, effectful forcing, E-groups, finite types, games,
  groups, injective types, integers, iterative types, lifting, locales,
  and the MLTT foundation.
- `snapshot/source/index.lagda:181-206` - metric/modal material, monads,
  naturals, decidability and order, ordinals, PCF, path sequences,
  quotients, rationals, reflexive graphs, relations, relative monads,
  slices, synthetic homotopy theory, taboos, TypeTopology proper, UF,
  W-types, wild categories, deprecated material, and gists.
- `snapshot/source/index.lagda:210-223` - safe-index scope and stable
  rendered-navigation advice.
- `snapshot/source/AllModulesIndex.lagda:1-48` - the complete import
  root and separation of safe, unsafe, and termination-check-disabled
  modules; `snapshot/source/AllModulesIndex.lagda:50-93` - global,
  infective, and coinfective option inventory.
- `snapshot/typetopology.agda-lib:1-3` - library include path and exact
  global flags.
- `snapshot/CONTRIBUTING.md:1-45` - research-first contribution and
  authorship policy; `snapshot/CONTRIBUTING.md:51-140` - source layout,
  literate-Agda style, notation, safety, and formatting conventions.
- `snapshot/AI-Policy.md:1` - AI-generated pull-request policy.

## Content digests

No corpus-wide mathematical digests are supplied. TypeTopology spans
hundreds of independently attributed developments, and a detached
digest would defeat the mandatory authorship and research-provenance
standard. When a result becomes relevant, read its local index and
defining module, then cite that exact material under the contract above.

## What the source establishes

This snapshot is the canonical formal corpus for the subjects its
individual modules present, under Lane's authority directive above.
Its safe root, broader all-modules root, explicit global flags, and
per-file research records allow a reader to distinguish the formal
status and provenance of each use. Authority does not license anonymous
reuse: every departure from a finding remains bound to the detailed
attribution standard in this entry.
