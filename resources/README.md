# resources/ — vetted source references

Each entry is one source (paper, book chapter, thesis, slide deck,
web reference) in its own directory: `resources/<slug>/`.

The directory serves two roles. It is the on-hand reference shelf
for the research materials this repository draws on — human and
agentic users alike open an entry to discover more about a source a
research artifact cites. And it is the citation store: an entry
carries **all the information needed to generate an academic
citation in the future** — full bibliographic record, the exact
document identity (hash + vintage), and where it came from.

**Information flows one way: from resources out, never from the
repository into resources.** An entry is self-contained — it
describes its source in the source's own terms and references at
most other entries in this tree, never modules, ledgers, notes, or
any research artifact elsewhere in the repository. Tracking what
*uses* a source is the job of the repository's own corpus (proof
artifacts, docs, the theorem ledger), which cites *into* this tree.
The repository is the moving target; this doctrine is what keeps an
entry durable against staleness as everything around it changes. A
repository reference appearing inside an entry is a defect.

An entry is built to serve a construction *at speed*: when a proof
turns on a source, the reader opens the vendored copy and jumps to
the cited line, so the map below is line-anchored, not vague.

## Canonical source format

House the source's own markup when it exists. The format hierarchy:

1. **Publication source** (`latex-source`) — LaTeX `.tex` (an arXiv
   e-print), or another publication's own markup. Math and structure
   stay intact and greppable; this is the canonical form for a
   document distributed as source rather than as a version-controlled
   research corpus.
2. **Repository source tree** (`source-tree`) — a deterministic archive
   of an immutable VCS revision containing a formal library, software
   artifact, research corpus, or mixed source tree. The full revision
   identifier is mandatory in `version:`. The readable extraction lives
   under `snapshot/` so the source repository's own custody files cannot
   collide with the entry README. For Git, build the canonical archive
   with `git archive` from the pinned commit rather than treating a
   forge-generated download archive as byte-stable.
3. **HTML** (`html`) — a web source whose published HTML is the form of
   record and is vendored directly.
4. **PDF** (`pdf`) — when no source markup is available.
5. **Scan** (`scan`) — a PDF whose page images, rather than an embedded
   text layer, are the form of record.
6. **Transcribed text** (`.pdftext`) — a `pdftotext` extraction, the
   lowest form: a greppability fallback beside a PDF when the source
   markup is absent. For a PDF lacking a text layer (a pure scan) or
   carrying a broken one, the pinned repair/OCR chain is
   **mandatory**, in order: `qpdf` to repair damaged structure when
   present, `ocrmypdf` to produce the text layer, then `pdftotext`
   over the result — never a hand transcription, never skipped, and
   never an unpinned OCR tool. An OCR-derived `.pdftext` is a
   locator only (grep targets and line anchors); digests and audits
   read the PDF pages directly (page renders), and the entry's
   Files section says so explicitly. Where any extraction — OCR or
   native — garbles load-bearing content (diagrams, glyphs,
   interleaved statements), the chain's final step is a **tracked
   correction patch**: each hunk verified against a page render by
   visual reasoning and itemized in the entry, applied mechanically
   after `pdftotext`, so the corrected `.pdftext` stays regenerable
   byte-identically (PDF + pinned chain + patch) and every
   editorial intervention is on the record. A correction never
   writes content a render does not show; applying or changing the
   patch is a re-extraction and voids the statement-audit field
   until the audit is re-run.

Each entry records its canonical format in its frontmatter
(`format: latex-source | source-tree | html | pdf | scan` — the schema
is below).
All vendored and derived forms are gitignored — the source tarball,
the extracted markup, the `.pdftext` — so only tracked, regenerable
metadata leaves the machine. A new unfolded-source file extension not
yet ignored is added to `.gitignore` as encountered.

## Entry format — `resources/<slug>/README.md`

Every entry README opens with **YAML frontmatter** — the
machine-parseable custody surface, the one home of the canonical
artifact's filename, its identity hashes, and its fetch URL. A
fetch or verify tool parses the frontmatter and nothing else
(`just resources-verify` reads it mechanically); the body sections
below carry the prose. The schema is deliberately flat — scalar
keys only, no nesting. Required keys, on every entry:

```yaml
---
artifact: <filename of the canonical artifact, in the entry dir>
sha256: <64-hex sha256 of the canonical artifact>
format: latex-source   # or: source-tree | html | pdf | scan
fetch-url: <URL that retrieves the canonical artifact, or none>
---
```

`fetch-url: none` is the explicit record that no public URL exists
(a user-supplied file, a paywalled source with no verified public
copy) — the field is never omitted. Optional keys, recorded only
when the entry actually has the datum (a field the source lacks is
omitted, never invented):

- `metadata-url:` — the source's metadata page (an arXiv abs URL).
- `doi:` — the DOI, bare (no resolver prefix).
- `version:` — the version pin: the version the fetch URL served
  at fetch time (an arXiv `v2`), or the full immutable VCS revision
  for a `source-tree`. This field is mandatory for `source-tree`.
- `fetched:` — the date the vendored artifact was obtained,
  `YYYY-MM-DD`.
- `sha256-inner:` — sha256 of the gunzip-decompressed inner form
  of the canonical artifact
  (`gunzip -c <artifact> | shasum -a 256`), the fallback identity
  should the gzip wrapper ever vary; it names no on-disk file and
  is not checked against disk.
- `secondary-artifact:` + `secondary-sha256:` — one additional
  vendored file worth pinning by hash (e.g. a
  superseded-but-retained compile); always a pair, verified
  against disk exactly like the canonical pair.

Re-fetching is mechanical from the frontmatter. For a directly hosted
artifact, retrieve `fetch-url`, name the result `artifact`, and verify
`sha256`, so no entry records fetch commands. For a `source-tree`, clone
`fetch-url`, check out `version`, reproduce the deterministic archive
described by the format rule above, and verify `sha256`. A re-fetch that
changes `sha256` is a re-ingestion: it voids the entry's `Statements
verified:` field until the audit is re-run, and a mismatch against the
recorded identity is FATAL (see Acquiring documents).

The body sections:

- **Citation** — full bibliographic record: authors, title, venue,
  year, DOI or arXiv id, URL.
- **Vetting** — who opened the document and when, and what it was
  checked to say. A directed agent ingestion produces a PROVISIONAL
  entry (say so here). **The load-bearing gate is the statement
  audit, not a signature**: an entry supports load-bearing citation
  once its identity is hash-verified and its statement audit is
  recorded; an entry with no recorded audit supports nothing. Two
  structured fields live here:
  - `Statements verified: N/M CONFIRMED (<depth>), <date>, by
    <agent>, @ <canonical-hash prefix>` — the independent
    statement audit of the content digests (the verifier's
    entry-statement-audit mode, dispatched by the lead after the
    entry is built; the contract's Ingestion section governs).
    **Load-bearing use requires this field.** A re-fetch, a
    re-extraction, or a digest addition or revision each change what
    the field's `N` and `M` cover, so each voids the field until the
    audit is re-run. The `@ <hash>` binding makes a re-fetch or
    re-extraction mechanical; a digest change is not hash-detectable,
    so `M` must grow and `N` must fall back whenever a digest is added
    or edited, by hand, in the same commit as the edit — `just
    resources-verify` reports a partial standing whenever `N < M`.
  - `Vetted: <date>, Lane` — Lane's discretion record, written only
    by Lane or at Lane's explicit direction; writing it retires the
    PROVISIONAL marker. Discretion is self-initiated, never a gate
    the pipeline queues behind: a citation on an audited-but-
    unvetted entry bears load and carries `audited; discretion
    pending` in the citing artifact's sidecar. A Lane veto retires
    the entry and voids every claim that leaned on it.
    `just resources-verify` lists where each entry stands.
- **Files** — an inventory of the vendored artifacts (the source
  tarball, the extracted markup or `.pdftext`), naming the canonical
  format and which file the reader greps. A `.pdftext` extraction
  records its **provenance**: the exact command chain and tool
  versions that produced it — `pdftotext` and its poppler always;
  for a scan, the mandatory `qpdf`/`ocrmypdf` repair/OCR steps and
  their versions too (all pinned by the flake; run inside
  `nix develop` — line anchors into an extraction are only as
  stable as the extractor chain), so the extraction is regenerable
  byte-identically, and an OCR-derived extraction is marked as
  such.
- **Source provenance** — where the document was actually obtained,
  as prose: who fetched it and when, from what kind of host, and
  every honesty caveat a re-fetcher needs — paywall status, a
  third-party host's non-persistence, an author page that has
  drifted to a different compile since the fetch. The fetch URL
  itself and the identity hashes live in the frontmatter (bind-once
  — this section narrates, never restates them, and carries no
  fetch commands). Backups of irreplaceable artifacts are handled
  outside the repository; the entry's job is to record identity
  (hash) and origin (URL) so any copy can be authenticated.
- **Section map** — a location→content map anchored to lines in the
  vendored readable copy (`l.NNN` into the `.tex`/`.pdftext`), with a
  jump note (`sed -n 'A,Bp' <file>`). Map **depth tracks the
  source's load**: a full line-anchored map for a load-bearing or
  mechanization-target source, a short outline for a background
  reference. A load-bearing citation resolves at `<file>:LINE`, not
  "Definition 1, §2".
- **Content digests** — the layer between the map and the source:
  statement-level digests of the load-bearing items, in the source's
  own terms and notation, each carrying its map anchor — so a reader
  can *use* a definition or theorem (its hypotheses, its shape)
  without opening the vendored copy. **Digest depth tracks the
  source's load**, like the map's: statement-level for the parts a
  development leans on, a few sentences per section for background
  parts, absent for a shelf reference. Digests state what the source
  states — never what any development has done with it. Render
  notation in Unicode, matching literate Agda and CLI reading, never
  in raw LaTeX. Write a multi-character subscript or superscript as
  `_{...}`/`^{...}` when Unicode has no combining form for it. Quote a
  source's own LaTeX macro name only as a labeled aside connecting a
  Unicode symbol back to the source, for example "`⟑` renders the
  source's `\tensorialand`", never as the symbol itself.
- **What the source establishes** — the source's actual deliverables
  and their status in the field, compactly. Entries record what the
  source states, not what anyone has proven from it: every
  mathematical claim here is CONJECTURED until machine-checked.

The depth standard: a full line-anchored map with content digests
for an implemented or load-bearing source, a one-line outline for a
background reference. The exemplar entry is `resources/rijke-hott/`.

## Acquiring documents

When a load-bearing claim rests on a source not yet vendored, the
default action is to ingest it (ingest-on-firsthand-need), producing
a PROVISIONAL entry — not merely to propose a candidate. Fetch by
stable identifier: for an arXiv source, `curl
https://arxiv.org/e-print/<id>` for the canonical LaTeX-source
tarball and `https://arxiv.org/abs/<id>` for metadata (the
paper-search capability maps this; feynman alpha is not relied on);
otherwise the source's stable URL or a user-supplied file. **Record
the fetch URL in the frontmatter** (`fetch-url:`; an explicit
`none` when no public URL exists) whenever a known URL sourced the
artifact — binding for PDFs, whose only stable identity otherwise is
the hash. Compute the sha256 of the canonical artifact and record
it as the frontmatter `sha256:`; for an existing entry, check it
against the recorded hash before citing from the local copy
(`just resources-verify` runs this check over the whole tree). A
hash mismatch is a FATAL finding: stop and resolve which document
the entry describes before citing anything.

An agent may ask to vendor a source at any time, especially when a
construction under development draws on it. Workflows also propose
candidate entries in their provenance sidecars; a PROVISIONAL entry
becomes vetted at the human confirmation step.
