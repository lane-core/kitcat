---
artifact: hott-should-eat-itself.html
sha256: 3a84d30b97fa9fbabac2946b33561b5ab2a96683c54fc4f08ee96a3a21bba1d7
format: html
fetch-url: https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/
version: live page fetched 2026-08-11
fetched: 2026-08-11
---

# Shulman - Homotopy Type Theory Should Eat Itself

Michael Shulman's problem statement about interpreting raw type-theoretic
syntax internally in HoTT and its connection with the problem of defining
semisimplicial types. The post records failed approaches through raw,
inductive-recursive, and inductive-inductive syntax and locates the common
obstruction in expressing infinitely coherent substitution and functoriality
without truncating the semantic universe.

Load declaration: research-problem reference, held at statement depth for the
main post only. Reader comments are preserved in the canonical HTML but are
not mapped or digested here.

## Citation

Michael Shulman. "Homotopy Type Theory Should Eat Itself (But So Far, It's Too
Big to Swallow)." *Homotopy Type Theory*, 3 March 2014.
<https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/>.

## Vetting

PROVISIONAL. Directed agent ingestion, 2026-08-11, from the URL supplied by
Lane for a comparison with Virtual Graph Theory. The main post was read in the
vendored HTML at the anchors below. No independent statement audit has been
run, so this entry supports no load-bearing citation.

## Files

- `hott-should-eat-itself.html` - canonical HTML artifact and the file the
  reader greps. It contains the post, its rendered mathematics as remote image
  references with LaTeX source in `alt` attributes, and the full comment
  thread. The vendored file has 7,416 lines; the post itself is at l.368-475.

## Source provenance

Fetched by agent on 2026-08-11 from the public WordPress-hosted Homotopy Type
Theory site using the user-supplied canonical post URL. The page is live and
includes mutable site furniture and comments, so the identity of this fetch is
the frontmatter hash rather than the URL alone.

## Section map

Line anchors are into `hott-should-eat-itself.html`; jump with
`sed -n 'A,Bp' hott-should-eat-itself.html`.

- l.368-386 - Title, authorship, status as a problem report, and the proposed
  internal interpretation of well-typed raw expressions.
- l.387-408 - Motivation for HoTT serving as its own metatheory.
- l.409-414 - Semisimplicial types: every externally fixed truncation can be
  generated, and an internal raw-syntax interpreter would turn such a
  generator into an internal construction.
- l.415-434 - Substitution obstruction and the regress from coherence at level
  `n` to coherence at level `n+1`.
- l.435-440 - Strict set-level syntax versus the higher semantic universe; the
  missing ability to express the universe's full coherence.
- l.441-470 - Structured syntax alternatives; truncation blocks interpretation
  into the universe, while omitting truncation leaves unresolved coercion and
  functoriality coherences.
- l.471-475 - Postscript: making propositional equality judgmental requires a
  coherence theorem showing that omitting its coercions loses no information.

## Content digests

- **Problem status** (l.374-375): the post announces no construction; it poses
  a problem and reports failed Agda experiments and a heuristic diagnosis.
- **Internal-metatheory problem** (l.377-386): define well-typed raw syntax
  inside type theory and interpret each well-typed expression into the ambient
  universe.
- **Semisimplicial reduction** (l.409-414): finite truncations are mechanically
  generable; an internal generator of raw expressions plus the desired
  interpreter would yield internal semisimplicial types.
- **Substitution regress** (l.432-434): interpreting substitution requires
  compatibility with composition of substitutions; coherence at dimension
  `n` calls for coherence at `n+1`.
- **Strictness mismatch** (l.436-439): raw syntax is strict and set-level, but
  the semantic universe is not; interpreting the former requires expressing
  the latter's full higher coherence.
- **Truncation dilemma** (l.456-468): infinitely many coherence constructors
  appear necessary without truncation, while set truncation prevents an
  interpretation into the non-set universe.
- **Infinite-objects conclusion** (l.469-470): the post conjecturally places the
  raw-syntax interpretation problem at roughly the same difficulty as the
  general problem of infinite coherent objects.
- **Judgmental-equality criterion** (l.471-475): a propositional equality can be
  omitted from notation as judgmental only when a coherence theorem shows that
  the omitted transport information carries no additional information.

## What the source establishes

No theorem is claimed. The post isolates a proposed internal-metatheory problem,
relates a solution to internal semisimplicial types, reports concrete failures
caused by substitution coherence, and offers the strict-syntax/higher-semantics
mismatch as a diagnosis. All mathematical conclusions remain CONJECTURED here
until machine-checked.
