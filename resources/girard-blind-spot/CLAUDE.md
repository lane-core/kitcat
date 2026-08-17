# girard-blind-spot — Jean-Yves Girard, *The Blind Spot: Lectures on Logic* (EMS, 2011)

A book-length course on logic (proof theory, the Curry–Howard correspondence, linear
logic, coherent spaces, ludics, and polarised classical logic), from lectures given at the
Université Franco-Italienne, Università Roma Tre, October to December 2004 (the book's own
acknowledgements). **[PDF]** — `girard-blind-spot.pdf` plus a cached `pdftotext` extraction
`girard-blind-spot.txt` (28k lines; greppable, jump with `sed -n 'A,Bp'`). Mathematical
glyphs are mostly preserved but some symbols render oddly (`⊢` as a backtick `` ` ``,
quotation marks as `«…»`); read the `.pdf` page for any formula that matters.

Files:
- `girard-blind-spot.pdf` — the book.
- `girard-blind-spot.txt` — the text extraction.

## Structure (section → line in `girard-blind-spot.txt`)

The table of contents is at lines ~90–430. Parts: I *The basics* (Ch. 1–4: sequent
calculus LK/LJ, the Hauptsatz), II *Around Curry–Howard* (Ch. 5–7: λ-calculus, System F,
cartesian closed categories), III *Linear logic* (Ch. 8–11: coherent spaces, the
perfect/imperfect connectives, phase semantics, proof-nets and the correctness
criterion), IV *Polarisation and beyond* (Ch. 12–16: polarised classical logic, ludics).

Loci most often consulted:

- **Coherent spaces** — §8.2 (line ~264 TOC; body in Ch. 8–9): the stable-maps model of
  linear logic; the basis of the "reflexive object in coherent spaces" route used
  elsewhere.
- **Linear logic, the connectives** — §9.2 perfect (multiplicative/additive),
  §9.3 imperfect (exponentials), §9.4 the logical system; proof-nets and the
  Danos–Regnier-style correctness criterion in Ch. 11 (§11.2–11.3).
- **Polarity** — introduced through the book (first noted §2.A.4, line ~1923; §4.A.1
  direct/indirect eliminations) and developed in Ch. 12 (§12.3 objections to
  polarisation; §12.A *Classical polarity*); positive = answer/expansive,
  negative = question/recessive.
- **§15.3 Categories and classical logic** (line 17385). The problem that a naïve
  categorical interpretation of classical logic collapses (the *double cut* (15.1)
  destroys both sides; the two reduction protocols (15.2)/(15.3) disagree — §15.3.1, line
  17386). The fix:
  - **§15.3.3 Comonoids** (line 17478) — individualise the proofs on which the two
    protocols give the same result.
  - **§15.3.4 Central morphisms** (line 17510). **Definition 74** (line 17511): a stable
    linear map `φ` from a comonoid `P` is *central* when it commutes with the sum and the
    neutral element. "Beyond linear maps, one must individualise those which are
    central. This will lead to the calculus LC" (line 17572). Centrality is the
    book's own terminology and origin (line 17570).
- **§15.4 The system LC** (line 417 TOC; body from ~17560). **§15.4.1 Stoups** (line
  17577): the sequent gets a *special zone, the stoup*, holding **at most one positive
  formula**; a sequent is written `⊢ Λ | Π` with the stoup `Π` carrying ≤ 1 positive
  formula. The interpretation of a proof of `⊢ Λ′ ; Λ″ | P` (Λ′ negative, Λ″ positive)
  is a *central* morphism (line 17585). Index entry "Stoup ⊢ |A" at line 27874 points to
  pp. 337, 339, 343, 348.
- **Ludics** (Ch. 13: designs, §13.1 designs-dessins / §13.2 designs-desseins).

The conjunction material of §15.3 is read elsewhere as an ordering phenomenon
(the non-canonical order of the conjuncts), and the stoup + central-morphism +
LC apparatus of §15.3–§15.4 is the polarised-classical backbone borrowed by
two-zone sequent presentations.
