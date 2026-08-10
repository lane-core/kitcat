---
artifact: rijke-hott.tar.gz
sha256: 562be57f5f652004b7f0a816a9196b417f661e1f21f203e7a99f1fa034cb628d
format: latex-source
fetch-url: https://arxiv.org/e-print/2212.11082
metadata-url: https://arxiv.org/abs/2212.11082
doi: 10.1017/9781108933568
version: v1
fetched: 2026-07-12
sha256-inner: 51ad7e31941f4959b8241c3e6c5518dac0cb750a87f731bc27cbe17a41a70b7f
---

# Rijke — Introduction to Homotopy Type Theory

The standard introductory text for univalent mathematics: a
self-contained development of Martin-Löf dependent type theory and
the univalent foundations, fixing the field's core vocabulary and
proof idioms — the identity type and path induction, equivalences,
contractibility, the h-level hierarchy, function extensionality,
univalence, and a first higher inductive type.

## Citation

Egbert Rijke. *Introduction to Homotopy Type Theory*.
arXiv:2212.11082 [math.LO], December 2022.
<https://arxiv.org/abs/2212.11082>. Published as a monograph:
*Cambridge Studies in Advanced Mathematics* 219, Cambridge
University Press, 23 October 2025, ISBN 9781108844161; DOI
10.1017/9781108933568 (per the CrossRef record, checked
2026-08-09).

## Vetting

Provisional marker retired 2026-07-13 (Vetted, below). Originally ingested: Ingested 2026-07-12 by Claude (Opus 4.8) at Lane's
direction, via the ingestion protocol: the arXiv LaTeX e-print
fetched directly, the canonical artifact hashed, and the source
tree read for the section map below. The document hash was checked
stable across two independent fetches. Content digests added
2026-07-13, statement-checked against the source at their anchors.
Provisional marker retired 2026-07-13 (Vetted, below); was: Lane's confirmation pending (the format authority
governs what the marker means).

Statements verified: 152/155 CONFIRMED on first pass, 3 CORRECTED
applied (full depth Part II; statement-lines full + paragraph
spot-checks Parts I/III), 2026-07-13, by verifier (Claude),
@ 562be57f; confirming re-pass clean 2026-07-13.

Vetted: 2026-07-13, Lane (ratified at Lane's explicit direction,
conveyed in-session; full-shelf ratification).

## Source errata

Two evident source typos, normalized faithful-to-intent in the
digests below (the normalized readings are what the digests state):

- `W-types.tex:19` — the induction principle prints `P(α(x))` for
  the intended `P(α(y))`; the intent is fixed by the computation
  rule at `W-types.tex:27` (the inductive hypotheses are at `α(y)`)
  and by the elementhood reformulation at `W-types.tex:343`.
- `W-types.tex:266` — the recursion body of the functorial action
  writes `W(f,g)` for the intended `W(f,e)`; no `g` is in scope,
  the definiendum declared at `W-types.tex:264` is `W(f,e)`, and
  every subsequent use (`:270`, `:301`) writes `W(f,e)`.

## Files

Canonical format: **LaTeX source** (an arXiv e-print). All vendored
and derived forms are gitignored; only this README is tracked.

- `rijke-hott.tar.gz` — the canonical artifact (the arXiv e-print
  source tarball). This is the file the frontmatter's canonical
  `sha256` is of.
- the extracted LaTeX tree beside it — `hott-intro.tex` (the main
  file: `\input`s the parts), the three part files
  (`chapter-type-theory.tex`, `chapter-univalent-foundations.tex`,
  `chapter-circle.tex`), and one `.tex` per lecture (mapped below),
  plus `bibliography.bib` and `cambridge7A.cls`.

Grep the lecture `.tex` for a definition; jump with
`sed -n 'A,Bp' <lecture>.tex`.

## Source provenance

Fetched from the arXiv e-print endpoint by stable identifier,
2026-07-12; the frontmatter carries the fetch and metadata URLs
and the identity hashes (canonical tarball plus the inner-tar
fallback). The canonical hash was checked stable across
independent arXiv fetches; a re-fetched tarball is extracted
beside itself with `tar xzf rijke-hott.tar.gz`. v1 is the only
arXiv version as of 2026-07-13.

## Section map

Three parts (`hott-intro.tex:170–172`), each `\input`ing one
`.tex` per lecture. Every lecture below lists its subsections and
its load-bearing definitions and theorems with the line in the
named `.tex` file, so a citation resolves at `<lecture>.tex:LINE`.
(Line numbers are of the vendored e-print source, hashed below.)

### Part I — Martin-Löf’s Dependent Type Theory (`chapter-type-theory.tex`)

#### `dtt.tex` — Dependent type theory

Develops the raw syntax of Martin-Löf dependent type theory: the four judgment forms, contexts as lists of variable declarations, type families and their sections, and the six sets of structural inference rules (conversion, substitution, weakening, generic element) that make derivations.

*Subsections:* Judgments and contexts in type theory (`:7`), Type families (`:79`), Inference rules (`:109`), Derivations (`:310`)

Key items:
- Definition — The four kinds of judgment in Martin-Löf type theory (A type; a : A; type equality; element equality, in context) `:32`
- Definition — Context — a finite list of variable declarations, each well-formed given the earlier ones `:59`
- Definition — Type family (indexed type): B(x) a type in context Γ, x : A `:83`
- Definition — Section of a type family — an element b(x) : B(x) in context Γ, x : A `:98`
- Definition — Fiber B(a) and value b(a): substitution of a term for the family's variable `:273`
- Definition — The structural rules — the six sets of inference rules underlying type dependency `:111`
- Definition — Variable conversion rules (stated once via a generic judgment thesis 𝒥) `:216`
- Definition — The substitution rule (generic judgment 𝒥 substituted along a : A) `:253`
- Definition — The weakening rule — extending the context by a fresh variable preserves judgments; constant/trivial family `:282`
- Definition — The generic element / variable rule — the hypothetical x : A is an element; provides the identity function `:302`

#### `pi.tex` — Dependent function types

Introduces dependent function types (Π-types) through their four principal rules — formation, introduction (λ-abstraction), elimination (evaluation), and computation (β/η) — then specializes to ordinary function types A→B and derives the identity function, composition, and the category laws (associativity and unit laws) for functions.

*Subsections:* The rules for dependent function types (`:8`), Ordinary function types (`:104`)

Key items:
- Definition — Π-formation rule (dependent function type ∏(x:A) B(x)) `:26`
- Definition — λ-abstraction (Π-introduction rule) `:46`
- Definition — evaluation (Π-elimination rule) `:71`
- Definition — β- and η-rules (Π-computation rules) `:87`
- Definition — ordinary function type A→B ≐ ∏(x:A) B `:115`
- Definition — identity function id_A : A→A `:225`
- Definition — composition of functions g∘f `:273`
- Lemma — associativity of function composition `:320`
- Lemma — left and right unit laws for composition (lem:fun_unit) `:350`

#### `nat.tex` — The natural numbers

Specifies ℕ as the archetypal inductive type via its four rule-sets (formation, introduction with zero and successor, induction principle, computation rules), then constructs addition by induction on ℕ and introduces pattern matching as the idiom for recursive definitions.

*Subsections:* The formal specification of the type of natural numbers (`:19`), Addition on the natural numbers (`:152`), Pattern matching (`:239`)

Key items:
- Definition — ℕ-formation rule (ℕ is postulated to be a type in the empty context) `:28`
- Definition — introduction rules: the zero element zeroℕ : ℕ and the successor function succℕ : ℕ → ℕ `:40`
- Definition — the induction principle indℕ (the type-theoretic elimination rule for ℕ: base case p₀ and inductive step pS) `:69`
- Remark — indℕ presented as a function; interderivability with the ℕ-ind rule `:89`
- Definition — computation rules for ℕ (base case indℕ(p₀,pS,zeroℕ) ≐ p₀ and inductive step indℕ(p₀,pS,succℕ n) ≐ pS(n, indℕ(...,n))) `:120`
- Definition — addition addℕ : ℕ → (ℕ → ℕ) defined by induction on the second variable (defn:addN) `:162`
- Remark — 0+n and succℕ(m)+n are not judgmental equalities; identifying them requires the identity type `:227`
- Definition — pattern matching as a presentation of definitions by the induction principle of ℕ `:263`

#### `inductive.tex` — More inductive types

Introduces the unit, empty, coproduct, integer, dependent-pair (Sigma), and cartesian-product types as inductive types via their constructors, induction principles, and computation rules, alongside negation and the propositions-as-types reading.

*Subsections:* The idea of general inductive types (`:7`), The unit type (`:17`), The empty type (`:50`), Coproducts (`:122`), The type of integers (`:200`), Dependent pair types (`:262`)

Key items:
- Definition — the unit type (1) with its induction principle `:23`
- Definition — the empty type (0) with its induction principle `:55`
- Definition — negation of types and is-empty (A -> 0) `:70`
- Proposition — negation is contravariant: (P -> Q) -> (not Q -> not P) `:93`
- Definition — the coproduct A + B with inl/inr and its induction principle `:125`
- Remark — functorial action of coproducts f + g `:158`
- Definition — the integers Z := N + (1 + N) `:208`
- Remark — the induction principle for the integers Z `:231`
- Definition — the dependent pair type (Sigma-type) with pairing and its induction principle `:269`
- Definition — the projection maps pr1 and pr2 `:292`
- Definition — the cartesian product A x B as a Sigma-type `:333`

#### `identity.tex` — Identity types

Introduces the identity type as an inductive family generated by refl, its path-induction principle, the groupoidal structure of types (concatenation, inversion, associativity, unit and inverse laws), the action on paths of functions, transport and dependent action on paths, and the contractibility of the total space of the identity type — closing with the addition laws on the natural numbers as a worked application.

*Subsections:* The inductive definition of identity types (`:13`), The groupoidal structure of types (`:76`), The action on identifications of functions (`:214`), Transport (`:276`), The uniqueness of refl (`:317`), The laws of addition on ℕ (`:350`)

Key items:
- Definition — the identity type and its induction principle (path induction / identification elimination) `:15`
- Definition — concatenation of identifications (transitivity) `:80`
- Definition — inverse operation on identifications (symmetry) `:107`
- Definition — the associator for concatenation `:135`
- Definition — left and right unit laws for concatenation `:164`
- Definition — left and right inverse laws for identifications `:182`
- Definition — the action on paths of a function (ap), with ap-id and ap-comp `:222`
- Definition — transport along an identification (tr_B) `:282`
- Definition — the dependent action on paths (apd) `:301`
- Proposition — contractibility of the total space of the identity type (uniqueness of (a,refl)) `:327`

#### `universes.tex` — Universes

Introduces type-theoretic universes (a type U with a universal family closed under the type formers), the "enough universes" postulate and its tower/join constructions, then uses universe-valued families to define observational equality on the naturals and characterize the identity type of N, proving Peano's seventh and eighth axioms.

*Subsections:* Specification of type theoretic universes (`:13`), Assuming enough universes (`:85`), Observational equality of the natural numbers (`:168`), Peano's seventh and eighth axioms (`:255`)

Key items:
- Definition — universe (type U with universal family Ty, closed under the type formers) `:31`
- Definition — enough universes (postulate: every finite list of types is contained in some universe) `:99`
- Definition — successor universe U+ (and the tower U, U+, U++, ...) `:123`
- Definition — observational equality Eq-N on the natural numbers (universe-valued binary relation by double induction) `:180`
- Lemma — Eq-N is reflexive (refl-Eq-N) `:214`
- Proposition — (m = n) <-> Eq-N(m,n): observational equality characterizes the identity type of N `:229`
- Theorem — succ-N is injective / Peano axiom P7: (m=n) <-> (succ m = succ n) `:265`
- Theorem — Peano axiom P8: zero is not a successor (0 != succ n) `:289`

#### `modular-arithmetic.tex` — Modular arithmetic via the Curry-Howard interpretation

Develops the Curry-Howard interpretation of logic (∃/∀ as Σ/Π) by building divisibility, the congruence relations on ℕ, the standard finite types Fin k, the effective split-surjective quotient map ℕ → Fin(k+1), and the cyclic groups ℤ/k as abelian groups.

*Subsections:* The Curry-Howard interpretation (`:7`), The congruence relations on ℕ (`:155`), The standard finite types (`:214`), The natural numbers modulo k+1 (`:300`), The cyclic groups (`:491`)

Key items:
- Definition — divisibility on ℕ (d ∣ n as a Σ-type) — the flagship Curry-Howard translation of ∃ `:19`
- Definition — typal binary relation; reflexive/symmetric/transitive; (typal) equivalence relation `:159`
- Definition — congruence modulo k (x ≡ y mod k := k ∣ dist(x,y)) `:181`
- Proposition — the congruence relation modulo k is an equivalence relation `:192`
- Definition — the standard finite types Fin k (recursive: Fin 0 := ∅, Fin(k+1) := Fin k + 1) `:230`
- Proposition — the inclusion natFin : Fin k → ℕ is injective `:287`
- Definition — split surjective (is-split-surjective f := Π(b:B) Σ(a:A) f(a)=b) — Curry-Howard surjectivity `:314`
- Definition — the quotient/reduction map [-]_{k+1} : ℕ → Fin(k+1) `:346`
- Theorem — effectiveness of the mod-(k+1) quotient map: [x]=[y] ↔ x ≡ y mod k+1 `:451`
- Theorem — the quotient map [-]_{k+1} : ℕ → Fin(k+1) is split surjective `:471`
- Definition — the cyclic groups ℤ/k (ℤ/0 := ℤ, ℤ/(k+1) := Fin(k+1)) `:494`
- Theorem — addition on ℤ/k satisfies the abelian group laws `:556`

#### `number-theory.tex` — Decidability in elementary number theory

Develops decidability in constructive number theory: decidable types and decidable equality, decidability of divisibility, the well-ordering principle of ℕ, the greatest common divisor defined by well-ordering, the infinitude of primes, and the Boolean reflection principle.

*Subsections:* Decidability and decidable equality (`:9`), Constructions by case analysis (`:126`), The well-ordering principle of ℕ (`:268`), The greatest common divisor (`:321`), The infinitude of primes (`:442`), Boolean reflection (`:542`)

Key items:
- Definition — decidable type (is-decidable A := A + ¬A) `:11`
- Definition — has-decidable-equality (decidable identity types) `:62`
- Lemma — decidability transports along a logical equivalence A ↔ B `:71`
- Theorem — divisibility d ∣ x is decidable on ℕ `:116`
- Corollary — bounded dependent product of decidable families is decidable `:254`
- Definition — lower bound and upper bound of a family over ℕ `:274`
- Theorem — well-ordering principle of ℕ (least witness of a decidable family) `:290`
- Definition — greatest common divisor (is-gcd characterization) `:333`
- Definition — gcd defined via the well-ordering principle `:401`
- Theorem — infinitude of primes (a prime exceeds every n) `:519`
- Theorem — Boolean reflection principle `:561`

### Part II — The Univalent Foundations of Mathematics (`chapter-univalent-foundations.tex`)

#### `equivalences.tex` — Equivalences

Introduces homotopies and the groupoid/whiskering structure on them, defines equivalence as a bi-invertible map (section + retraction) and relates it to having an inverse, and characterizes the identity types of Sigma-types via observational equality.

*Subsections:* Homotopies (`:12`), Bi-invertible maps (`:154`), Characterizing the identity types of Σ-types (`:313`)

Key items:
- Definition — homotopy (f ~ g) as a family of pointwise identifications `:36`
- Proposition — homotopies satisfy the groupoid laws (assoc, unit, inverse up to homotopy) `:99`
- Definition — whiskering operations on homotopies (h . H and H . f) `:139`
- Definition — sections, retractions, and is-equiv (equivalence as a bi-invertible map) `:158`
- Remark — has-inverse(f) (invertible map) versus is-equiv(f), and why they differ `:206`
- Proposition — is-equiv(f) implies has-inverse(f) (every equivalence can be given an inverse) `:225`
- Corollary — the inverse of an equivalence is again an equivalence `:248`
- Definition — Eq-Sigma: observational equality on Sigma-types `:348`
- Definition — pair-eq : (s = t) -> Eq-Sigma(s,t) `:374`
- Theorem — pair-eq is an equivalence (characterization of identity types of Sigma-types) `:382`

#### `contractible.tex` — Contractible types and contractible maps

Develops contractibility (is-contr) and singleton induction, then defines contractible maps (fibers), and proves the two-way equivalence between being an equivalence and being a contractible map via coherently invertible maps.

*Subsections:* Contractible types (`:20`), Singleton induction (`:58`), Contractible maps (`:131`), Equivalences are contractible maps (`:210`)

Key items:
- Definition — is-contr (contractible type: center + contraction) `:22`
- Theorem — total space of the identity type Σ(x:A) a=x is contractible `:42`
- Definition — singleton induction (ev-pt has a section) `:64`
- Theorem — A is contractible iff A is pointed and satisfies singleton induction `:89`
- Definition — fiber of a map fib(f,b) := Σ(a:A) f(a)=b `:134`
- Definition — contractible map is-contr(f) := all fibers contractible `:189`
- Theorem — any contractible map is an equivalence `:196`
- Definition — coherently invertible map (g,G,H,K with the extra coherence) `:226`
- Proposition — any coherently invertible map has contractible fibers `:239`
- Lemma — has-inverse(f) → is-coh-invertible(f) `:321`
- Theorem — any equivalence is a contractible map `:362`

#### `fundamental.tex` — The fundamental theorem of identity types

Develops the fundamental theorem of identity types — a type family with a point is an identity system iff its total space is contractible iff the canonical family of maps out of the identity type is a family of equivalences — and applies it to characterize identity types of ℕ, embeddings, disjointness of coproducts, and the structure identity principle.

*Subsections:* Families of equivalences (`:16`), The fundamental theorem (`:144`), Equality on the natural numbers (`:222`), Embeddings (`:289`), Disjointness of coproducts (`:336`), The structure identity principle (`:425`)

Key items:
- Definition — the total map tot(f) of a family of maps `:19`
- Lemma — the fiber of tot(f) at t is equivalent to the fiber of f(pr1 t) at pr2 t `:31`
- Theorem — f is a family of equivalences iff tot(f) is an equivalence `:61`
- Definition — (unary) identity system on A at a `:152`
- Theorem — the fundamental theorem of identity types (fam-of-equivs / contractible total space / identity system) `:181`
- Theorem — characterization of the identity type of the natural numbers (m=n) ≃ EqN(m,n) `:242`
- Definition — embedding: is-emb(f) via ap f being an equivalence `:293`
- Theorem — any equivalence is an embedding `:306`
- Theorem — identity types of coproducts / disjointness of coproducts `:345`
- Theorem — the structure identity principle `:450`

#### `hierarchy.tex` — Propositions, sets, and the higher truncation levels

Builds the h-level (truncation) hierarchy from the bottom up: propositions and sets as the first two levels above contractibility, embeddings and subtypes as their map-level counterparts, Hedberg's theorem, and the general is-trunc hierarchy with its closure properties.

*Subsections:* Propositions (`:21`), Subtypes (`:96`), Sets (`:191`), General truncation levels (`:288`)

Key items:
- Definition — is-prop (proposition: a type with contractible identity types) `:24`
- Proposition — characterizations of is-prop (prop iff all-elements-equal, etc.) `:45`
- Proposition — map between propositions is an equivalence iff a map back exists (P≃Q ↔ P↔Q) `:80`
- Definition — subtype / property (a proposition-valued type family) `:111`
- Theorem — f is an embedding iff every fiber is a proposition `:151`
- Definition — is-set (set: a type with propositional identity types) `:194`
- Theorem — set criterion: a prop-valued reflexive relation implying identity makes A a set `:228`
- Theorem — Hedberg's theorem (decidable equality implies set) `:261`
- Definition — is-trunc: the h-level / truncation hierarchy defined by recursion on k `:312`
- Proposition — truncation levels are cumulative: a k-type is a (k+1)-type `:343`
- Theorem — f is (k+1)-truncated iff ap_f is k-truncated on all identity types `:386`

#### `funext.tex` — Function extensionality

Develops the function extensionality axiom and its equivalent forms (including weak funext), then applies it: closure of h-levels under Π, type-theoretic choice and identity systems on Π-types, the dependent universal properties of Σ- and identity types, precomposition by an equivalence, and strong induction on ℕ.

*Subsections:* Equivalent forms of function extensionality (`:28`), Identity systems on Π-types (`:153`), Universal properties (`:282`), Composing with equivalences (`:378`), The strong induction principle of ℕ (`:462`)

Key items:
- Proposition — the three equivalent forms of function extensionality at f (htpy-eq is an equivalence / total space of homotopies is contractible / homotopy induction), via the fundamental theorem `:32`
- Theorem — function extensionality ⟺ weak function extensionality (a Π of contractible types is contractible) `:63`
- Axiom — the Function Extensionality axiom (htpy-eq : (f=g) → (f ~ g) is an equivalence; inverse eq-htpy) `:111`
- Theorem — a Π of a family of k-types is a k-type (h-levels close under Π) `:132`
- Theorem — type-theoretic choice: distributivity of Π over Σ is an equivalence `:157`
- Theorem — identity systems on Π-types (Eq-Pi from pointwise identity systems) `:262`
- Theorem — the dependent universal property of Σ-types (ev-pair is an equivalence) `:297`
- Theorem — the dependent universal property of identity types / type-theoretic Yoneda lemma (ev-refl is an equivalence) `:350`
- Theorem — f is an equivalence iff precomposition by f is an equivalence `:382`
- Theorem — strong induction principle for the natural numbers `:468`

#### `propositional-truncation.tex` — Propositional truncations

Specifies the propositional truncation of a type by its universal property (precomposition into propositions is an equivalence), constructs it as a higher inductive type with its induction principle, uses it to interpret disjunction and existential quantification, and (via Kraus's theorem) extends weakly constant maps into sets.

*Subsections:* The universal property of propositional truncations (`:14`), Propositional truncations as higher inductive types (`:103`), Logic in type theory (`:256`), Mapping propositional truncations into sets (`:342`)

Key items:
- Definition — is a propositional truncation (universal property: precomposition ∘f : (P→Q)→(A→Q) is an equivalence for every proposition Q) `:22`
- Proposition — propositional truncation is unique up to equivalence (3-for-2 property of propositional truncations) `:56`
- Lemma — ∥A∥ is a proposition `:146`
- Definition — induction principle of the propositional truncation ∥A∥ `:178`
- Theorem — η : A → ∥A∥ satisfies the universal property of the propositional truncation `:213`
- Definition — disjunction P ∨ Q := ∥P+Q∥ `:263`
- Definition — existential quantification ∃_{x:A} P(x) := ∥Σ_{x:A} P(x)∥ `:292`
- Definition — weakly constant map (is-weakly-constant(f) := Π_{x,y:A} f(x)=f(y)) `:390`
- Theorem — Kraus: a weakly constant map into a set B extends uniquely along η, i.e. (∥A∥→B) ≃ Σ_{f:A→B} Π_{x,y} f(x)=f(y) `:424`

#### `images.tex` — Image factorizations

Constructs the image of a map via propositional truncation as the least embedding through which the map factors — proving its universal property and uniqueness — then develops surjective maps, the unique surjection-then-embedding factorization, and Cantor's diagonal theorem.

*Subsections:* The image of a map (`:12`), Surjective maps (`:205`), Cantor's diagonal argument (`:351`)

Key items:
- Definition — morphism from f to g over X (hom-slice hom_X(f,g)) `:20`
- Definition — universal property of the image of a map `:38`
- Definition — the image im(f) := Σ(x:X) ‖fib_f(x)‖, with image inclusion i_f `:96`
- Theorem — the image inclusion i_f satisfies the universal property of the image `:132`
- Theorem — uniqueness of the image up to equivalence (two-of-three property) `:157`
- Definition — surjective map, is-surj(f) := Π(b:B) ‖fib_f(b)‖ `:209`
- Proposition — dependent universal property of surjective maps (surjectivity characterized by precomposition equivalence) `:226`
- Theorem — m satisfies the image universal property iff q is surjective `:284`
- Corollary — every map factors uniquely as a surjection followed by an embedding `:332`
- Definition — the U-power set P_U(X) := X → Prop_U `:356`
- Theorem — Cantor's theorem: no surjection X → P_U(X) `:363`

#### `finite-types.tex` — Finite types

Develops finite types in univalent mathematics: countings (Fin k ≃ A) and their closure properties, the double-counting theorem that Fin k ≃ Fin l forces k = l, and the propositionally-truncated notion of finiteness with a well-defined cardinality and its closure under coproducts, products, and Σ.

*Subsections:* Counting in type theory (`:3`), Double counting in type theory (`:129`), Finite types (`:240`)

Key items:
- Definition — cnt(A) — countings of a type (Σ(k:ℕ) Fin k ≃ A) `:7`
- Theorem — closure of countings under coproducts and Σ (thm:count) `:39`
- Corollary — countings and cartesian products (cor:count-prod) `:112`
- Proposition — Maybe is injective: (X+1 ≃ Y+1) → (X ≃ Y) (prp:is-injective-maybe) `:138`
- Theorem — double counting: (Fin k ≃ Fin l) → (k = l) (thm:is-injective-Fin) `:219`
- Definition — is-finite(X), the type 𝔽 of finite types, and BS_k (defn:finite) `:244`
- Theorem — is-finite'(X) := Σ(k:ℕ)‖Fin k ≃ X‖ is a proposition and is logically equivalent to is-finite(X); the unique k is the cardinality |X| `:272`
- Corollary — 𝔽 ≃ Σ(k:ℕ) BS_k `:307`
- Proposition — principle of finite choice (prp:finite-choice) `:324`
- Theorem — closure of finite types under coproduct, product, and Σ `:346`

#### `univalence.tex` — The univalence axiom

Introduces the univalence axiom as the characterization of a universe's identity type, deriving its equivalent forms (equivalence induction), propositional extensionality, Voevodsky's theorem that univalence implies function extensionality, the object/subtype classifiers, and the failure of global choice.

*Subsections:* Equivalent forms of the univalence axiom (`:11`), Propositional extensionality (`:110`), Univalence implies function extensionality (`:177`), Maps and families of types (`:245`), Classical mathematics with the univalence axiom (`:345`), The binomial types (`:464`)

Key items:
- Theorem — univalence in three equivalent forms: equiv-eq is an equivalence / Sigma(B, A≃B) contractible / equivalence induction `:14`
- Axiom — the univalence axiom (all universes are univalent; eq-equiv is the inverse of equiv-eq) `:49`
- Theorem — propositional extensionality: iff-eq is an equivalence, so Prop_U is a set `:143`
- Lemma — post-composition by an equivalence is an equivalence (via equivalence induction) `:180`
- Theorem — univalence implies function extensionality (Voevodsky) `:198`
- Theorem — object classifier: Sigma(X:U, X→A) ≃ (A→U) via fibers `:249`
- Theorem — subuniverse classifier (families with fiberwise structure P classify maps into U_P) `:295`
- Corollary — subtypes of A are equivalently embeddings X↪A, i.e. Sigma(X, X↪A) ≃ (A→Prop_U) `:319`
- Corollary — no global choice function Prod(A:U, ‖A‖→A) — incompatible with univalence `:395`

#### `set-quotients.tex` — Set quotients

Constructs the quotient of a type by an equivalence relation as its type of equivalence classes, proves the universal property of set quotients and its equivalent characterizations (surjective + effective, image factorization), tames size via the replacement axiom, and applies the machinery to partitions, unique representatives (the rationals), and set truncation.

*Subsections:* Equivalence relations and the replacement axiom (`:14`), The universal property of set quotients (`:146`), Partitions (`:395`), Unique representatives of equivalence classes (`:486`), Set truncations (`:609`)

Key items:
- Definition — equivalence relation (prop-valued reflexive/symmetric/transitive R : A → A → Prop_U) `:16`
- Definition — equivalence class and the set quotient A/R as the type of equivalence classes ([x]_R = R(x), q_R) `:26`
- Proposition — characterization of the identity type of A/R: ([x]_R = P) ≃ P(x) `:48`
- Corollary — effectivity of the quotient map: ([x]_R = [y]_R) ≃ R(x,y) `:76`
- Definition — locally U-small type/map (identity types are U-small) `:97`
- Axiom — the replacement axiom (image of a U-small type into a locally U-small type is U-small) `:122`
- Definition — universal property of the set quotient (unique extension of R-invariant maps into sets) `:159`
- Theorem — three equivalent characterizations of a set quotient: universal property ⇔ surjective + effective ⇔ image factorization of R `:189`
- Theorem — Eq-Rel_U(A) ≃ Σ(X : Set_U) A ↠ X (equivalence relations ≃ surjections into sets) `:350`
- Theorem — unique representatives give the quotient: q : A → Σ(x:A) C(x) is a set quotient `:499`
- Definition — set truncation (f : A → B into a set B universal for maps into sets) `:622`
- Theorem — equivalent characterizations of set truncation: universal ⇔ dependent universal ⇔ surjective + effective for ‖x=y‖ `:632`

#### `groups.tex` — Groups in univalent mathematics

Builds the type of all groups (via semigroups and monoids), proves isomorphic groups are equal using the fundamental theorem of identity types and the structure identity principle, then defines homotopy groups via iterated loop spaces and proves them abelian for n≥2 by the Eckmann-Hilton argument.

*Subsections:* The type of all groups (`:12`), Group homomorphisms (`:107`), Isomorphic groups are equal (`:176`), Homotopy groups of types (`:267`), The Eckmann-Hilton argument (`:380`), Concrete versus abstract groups in univalent mathematics (`:523`)

Key items:
- Definition — semigroup (set + associative binary operation) `:22`
- Lemma — is-unital(G) is a proposition (being unital is a property, not structure) `:48`
- Definition — is-group / group (unital semigroup with inverses) `:59`
- Definition — group homomorphism (operation-preserving map) `:109`
- Definition — is-iso / isomorphism of (semi)groups `:146`
- Lemma — a homomorphism is an iso iff its underlying map is an equivalence (lem:grp_iso) `:178`
- Theorem — iso-eq is a family of equivalences for semigroups (via fundamental theorem + structure identity principle) `:202`
- Theorem — isomorphic groups are equal (iso-eq is an equivalence) `:244`
- Definition — loop space and iterated loop space Ω^n `:283`
- Definition — n-th homotopy group π_n and the fundamental group π_1 `:301`
- Theorem — Eckmann-Hilton: p∙q = q∙p for double loops `:477`
- Theorem — truncated generalization of the fundamental theorem of identity types (thm:truncated-fundamental) `:580`

#### `W-types.tex` — General inductive types

Develops general inductive types via W-types (well-founded trees): their construction, observational/identity characterization, truncation levels, functorial action, the elementhood and well-founded induction relation, extensionality, and the multiset model culminating in Russell's paradox that a univalent universe is not small.

*Subsections:* The type of well-founded trees (`:10`), Observational equality of W-types (`:164`), Functoriality of W-types (`:255`), The elementhood relation on W-types (`:320`), Extensional W-types (`:404`), Russell's paradox in type theory (`:488`)

Key items:
- Definition — W-type W(A,B) (well-founded trees) with constructor tree/collect `:12`
- Definition — observational equality relation EqW on W(A,B) `:197`
- Theorem — EqW characterizes the identity type of W(A,B) (canonical map is an equivalence) `:208`
- Theorem — if A is a (k+1)-type then so is W(A,B) (W-types preserve truncation level) `:240`
- Definition — functorial action W(f,e) of a map plus family of equivalences on W-types `:259`
- Theorem — if f is k-truncated then W(f,e) is; in particular equivalences and embeddings are preserved `:301`
- Definition — elementhood relation ∈ on W(A,B) `:330`
- Theorem — well-founded induction principle for the elementhood relation on W-types `:340`
- Definition — extensional W-type (canonical map to shared-elements equivalence) `:419`
- Theorem — characterization of extensionality for an inhabited W-type (equivalent conditions) `:429`
- Definition — type of multisets M_U := W(U, Ty) `:502`
- Theorem — Russell's paradox: a univalent universe U cannot be U-small `:693`

### Part III — The circle: synthetic homotopy theory (`chapter-circle.tex`)

#### `circle.tex` — The circle

Introduces the circle S¹ as a higher inductive type: its induction principle, the (dependent) universal property identifying maps out of S¹ with free loops, and the coherent H-space multiplicative structure on the circle.

*Subsections:* The induction principle of the circle (`:7`), The (dependent) universal property of the circle (`:83`), Multiplication on the circle (`:248`)

Key items:
- Definition — dependent action on generators dgen_{S¹} `:26`
- Definition — the circle S¹ (base, loop) and its induction principle `:40`
- Remark — identifications in Σ(u:P(base)) tr_P(loop,u)=u as commuting squares `:57`
- Theorem — the dependent universal property of the circle (dgen_{S¹} is an equivalence) `:102`
- Theorem — the universal property of the circle (maps S¹→X ≃ free loops Σ(x:X) x=x) `:181`
- Corollary — contractibility of maps S¹→X realizing a given loop `:228`
- Definition — H-space structure and coherent unit laws `:258`
- Theorem — the H-space (multiplicative) structure on the circle `:284`

#### `circle-universal-cover.tex` — The universal cover of the circle

Uses univalence to build the universal cover of the circle as a family of sets S¹→Set via descent data, proves the dependent universal property of the integers, shows the universal cover is an identity system (so the circle is a 1-type), and derives the group isomorphism π₁(S¹)≅ℤ.

*Subsections:* The universal cover of the circle (`:8`), Working with descent data (`:100`), The (dependent) universal property of the integers (`:238`), The fundamental group of the circle (`:371`)

Key items:
- Definition — descent data for the circle: the type family D(X,e) from (X, e:X≃X) `:18`
- Definition — the universal cover E := D(ℤ, succ) of the circle `:71`
- Lemma — segment of the helix: path lifting of loop in the total space `:84`
- Proposition — sections of A over S¹ are equivalently fixed points of e:X≃X `:145`
- Corollary — families of maps out of the universal cover as succ/e-equivariant maps ℤ→X `:209`
- Lemma — ℤ-induction (elim-ℤ) from a base point and an equivalence e_k:B(k)≃B(k+1) `:246`
- Proposition — dependent universal property of ℤ (uniqueness/contractibility) `:297`
- Corollary — universal property of ℤ used for the fundamental group (ev₀ an equivalence) `:359`
- Theorem — the universal cover of the circle is an identity system at base `:377`
- Corollary — the circle is a 1-type and not a 0-type `:397`
- Proposition — fundamental theorem of identity types augmented with a binary operation `:417`
- Theorem — the fundamental group of the circle: π₁(S¹)≅ℤ `:446`

## Content digests

Statement-level digests of the load-bearing items, in the source's
own terms and notation, each anchored into the vendored `.tex` at
the same lines as the section map — so a definition or theorem is
usable from the digest alone, and the anchor opens the full text.
Depth follows load: Part II (the univalent-foundations core) is
digested in full; Parts I and III carry lighter digests, with
statement lines only for the items most leaned on (the identity-
type calculus, the circle's induction principle and π₁(S¹) ≅ ℤ).
Digests state, never prove; every claim is the source's.

### Part I — Martin-Löf’s Dependent Type Theory

#### `dtt.tex` — Dependent type theory

Sets up the raw syntax of Martin-Löf dependent type theory before any type former is introduced. Fixes the four kinds of judgment — A type, a : A, judgmental equality of types A ≐ B, and judgmental equality of elements a ≐ b, each in a context Γ — and defines contexts as finite lists of variable declarations, each well-formed relative to the earlier ones. Type families B over A and their sections b(x) : B(x) are the basic dependent notions, with the fiber B(a) and value b(a) obtained by substitution. The heart of the lecture is the six sets of structural inference rules that govern type dependency: the equivalence and conversion rules for judgmental equality, variable conversion (stated once via a generic judgment 𝒥), substitution, weakening, and the generic element rule x : A ⊢ x : A, which yields the identity function. Closes by assembling these rules into derivation trees, the formal notion of proof in the theory.

#### `pi.tex` — Dependent function types

Introduces the dependent function type Π (x:A) B(x) through its four principal rules: formation, introduction by λ-abstraction, elimination by evaluation, and the β- and η-computation rules. Ordinary function types A → B are then the special case of a Π over a constant family, with their own instances of the rules spelled out. On this basis the lecture defines the identity function id_A : A → A and composition g ∘ f, and proves the category laws for functions: associativity of composition and the left and right unit laws with respect to id. These constructions are the first worked examples of reasoning with the inference rules from the preceding lecture.

#### `nat.tex` — The natural numbers

Presents ℕ as the archetypal inductive type via its four rule sets: formation, the introduction rules 0ℕ : ℕ and succℕ : ℕ → ℕ, the induction principle indℕ (a section of any family P over ℕ from a base case p₀ : P(0ℕ) and an inductive step pS : Π (n:ℕ) P(n) → P(succℕ(n))), and the computation rules identifying indℕ on 0ℕ and succℕ(n) judgmentally. Addition addℕ : ℕ → (ℕ → ℕ) is constructed by induction on the second argument, so that m + 0 ≐ m and m + succℕ(n) ≐ succℕ(m + n) hold judgmentally. The lecture notes that the companion laws 0 + n = n and succℕ(m) + n = succℕ(m + n) are not judgmental, motivating the identity type introduced two lectures later. Closes by introducing pattern matching as a readable presentation of definitions given by the induction principle.

#### `inductive.tex` — More inductive types

Extends the inductive-type toolkit beyond ℕ, giving each new type by its constructors, induction principle, and computation rules. The unit type 1 and the empty type ∅ come first, with negation ¬A := A → ∅ and the proof that negation is contravariant: (P → Q) → (¬Q → ¬P). Coproducts A + B follow, with inl/inr, their induction principle, and the functorial action f + g; the integers are then defined as ℤ := ℕ + (1 + ℕ), with an induction principle proceeding by cases on the negatives, zero, and the positives. Dependent pair types Σ (x:A) B(x) are introduced with the pairing constructor and Σ-induction, from which the projections pr1 and pr2 are derived; the cartesian product A × B is the Σ-type over a constant family. Throughout, the lecture reads these formers through the propositions-as-types interpretation.

#### `identity.tex` — Identity types

Introduces the identity type as an inductive family generated by reflexivity, and develops the path algebra every later lecture uses. From path induction alone it constructs the groupoidal structure of a type — concatenation, inverses, the associator, and the unit and inverse laws, each an identification of identifications rather than a judgmental equality — followed by the action on paths of functions and the transport structure of type families. The uniqueness of refl is made precise as the contractibility of the total space Σ (x:A) a = x, the germ of the contractibility developments of Part II. The lecture closes by proving the unit laws, successor laws, associativity, and commutativity of addition on ℕ as the first sustained equational development.

- **Definition (the identity type and path induction) `:15`** — for a : A, the identity type a =_A x is the inductive family indexed by x : A with sole constructor refl_a : a =_A a. Its induction principle (path induction, identification elimination) gives for any family P(x, p) a function path-ind_a : P(a, refl_a) → Π (x:A) Π (p : a =_A x) P(x, p) with path-ind_a(u, a, refl_a) ≐ u.
- **Definition (concatenation) `:80`** — the operation concat : Π (x,y,z:A) (x = y) → ((y = z) → (x = z)), written p ∙ q, constructed by path induction; the associator (`:135`), the left and right unit laws (`:164`), and the left and right inverse laws (`:182`) are constructed for it, all by path induction.
- **Definition (inverse) `:107`** — the operation inv : Π (x,y:A) (x = y) → (y = x), written p⁻¹, sending refl_x to refl_x.
- **Definition (action on paths) `:222`** — for f : A → B, the operation ap_f : Π (x,y:A) (x = y) → (f(x) = f(y)), together with ap-id : p = ap_{id}(p) and ap-comp : ap_g(ap_f(p)) = ap_{g∘f}(p); ap_f moreover preserves refl, inverses, and concatenation (`:249`).
- **Definition (transport) `:282`** — for a type family B over A, the operation tr_B : Π (x,y:A) (x = y) → (B(x) → B(y)) with tr_B(refl_x) ≐ id_{B(x)}; it underlies the dependent action on paths apd_f(p) : tr_B(p, f(x)) = f(y) of a dependent function f (`:301`).
- **Proposition (contractibility of the total space of the identity type) `:327`** — for any a : A there is an identification (a, refl_a) = y for every y : Σ (x:A) a = x, so the pair (a, refl_a) is unique up to identification in the total space of the identity type.

#### `universes.tex` — Universes

Specifies type-theoretic universes: a universe is a type 𝒰 equipped with a universal family Ty over it, closed under the type formers, so that universe-valued maps A → 𝒰 present type families over A. The text then assumes "enough universes" — for every finite list of types there is a universe containing them — and constructs from that assumption the base universe 𝒰₀, successor universes 𝒰⁺, and joins 𝒰 ⊔ 𝒱. The payoff is that families of types can now be defined by induction: observational equality Eq-ℕ on the natural numbers is a universe-valued binary relation defined by double induction, proven reflexive, and shown to characterize the identity type via (m = n) ↔ Eq-ℕ(m, n). As applications the lecture proves Peano's seventh axiom — succℕ is injective, in the form (m = n) ↔ (succℕ(m) = succℕ(n)) — and Peano's eighth axiom, that 0ℕ is not a successor.

#### `modular-arithmetic.tex` — Modular arithmetic via the Curry-Howard interpretation

Develops the Curry-Howard interpretation of logic — ∃ as Σ, ∀ as Π — with divisibility d ∣ n := Σ (k:ℕ) d·k = n as the flagship translation. Typal binary relations and (typal) equivalence relations are defined, and congruence modulo k, given by x ≡ y mod k := k ∣ dist(x, y), is proven an equivalence relation. The standard finite types are built recursively — Fin 0 := ∅, Fin (k+1) := Fin k + 1 — with an injective inclusion Fin k → ℕ, and the reduction map [–]_{k+1} : ℕ → Fin (k+1) is constructed and shown to be effective ([x] = [y] ↔ x ≡ y mod k+1) and split surjective, where split surjectivity is the Curry-Howard reading Π (b:B) Σ (a:A) f(a) = b. The lecture ends by defining the cyclic groups ℤ/k — ℤ/0 := ℤ and ℤ/(k+1) := Fin (k+1) — and proving that their addition satisfies the abelian group laws.

#### `number-theory.tex` — Decidability in elementary number theory

Develops decidability as the constructive engine of elementary number theory. A type is decidable when is-decidable(A) := A + ¬A holds, and a type has decidable equality when all its identity types are decidable; decidability transports along logical equivalences, ℕ and the Fin k have decidable equality, and divisibility on ℕ is decidable. Constructions by case analysis give closure properties, including decidability of bounded dependent products over decidable families. On this basis the lecture proves the well-ordering principle of ℕ — every decidable family with a witness has a least one — and uses it to define the greatest common divisor, characterized by is-gcd. It concludes with the infinitude of primes (for every n there is a prime exceeding it) and the Boolean reflection principle, which lets decidable propositions be proven by computation.

### Part II — The Univalent Foundations of Mathematics

#### `equivalences.tex` — Equivalences

Defines what it means for a map to be an equivalence, deliberately so that is-equiv(f) will be a *property* of maps rather than structure — the naive "has an inverse" definition fails this. The lecture first develops homotopies (pointwise identifications) with their groupoid and whiskering structure, then defines equivalence as a bi-invertible map and relates it to invertibility, and closes by characterizing the identity types of Σ-types via observational equality.

- **Definition (homotopy) `:36`** — for dependent functions f, g : Π (x:A) B(x), the type of homotopies is f ~ g := Π (x:A) f(x) = g(x), the type of pointwise identifications. Since f ~ g is itself a dependent function type, homotopies between homotopies H ~ K := Π (x:A) H(x) = K(x) make sense. Motivating example: neg-neg-bool : neg ∘ neg ~ id on bool, where the identification neg ∘ neg = id is not constructible.
- **Definition (groupoid operations on homotopies) `:77`** — refl-htpy(f) := λx. refl; inv-htpy(H) := λx. H(x)⁻¹ (written H⁻¹); concat-htpy(H, K) := λx. H(x) ∙ K(x) (written H ∙ K) — all defined pointwise from the operations on identifications.
- **Proposition (groupoid laws of homotopies) `:99`** — homotopies satisfy the groupoid laws *up to homotopy*: assoc-htpy(H,K,L) : (H ∙ K) ∙ L ~ H ∙ (K ∙ L) for H : f ~ g, K : g ~ h, L : h ~ i; left/right unit laws refl-htpy_f ∙ H ~ H and H ∙ refl-htpy_g ~ H; left/right inverse laws H⁻¹ ∙ H ~ refl-htpy_g and H ∙ H⁻¹ ~ refl-htpy_f.
- **Definition (whiskering) `:139`** — for H : f ~ g with f, g : A → B and h : B → C, define h · H := λx. ap h (H(x)) : h ∘ f ~ h ∘ g; for f : A → B and H : g ~ h with g, h : B → C, define H · f := λx. H(f(x)) : g ∘ f ~ h ∘ f.
- **Definition (sections, retractions, is-equiv, ≃) `:158`** — sec(f) := Σ (g : B → A) f ∘ g ~ id_B; retr(f) := Σ (h : B → A) h ∘ f ~ id_A (if f has a retraction, A is called a retract of B); f is an equivalence if it has both: is-equiv(f) := sec(f) × retr(f); A ≃ B := Σ (f : A → B) is-equiv(f). For an equivalence e, e⁻¹ is defined to be the section of e. An equivalence is thus a *bi-invertible* map, with separate right inverse (g, G : f∘g ~ id_B) and left inverse (h, H : h∘f ~ id_A).
- **Remark (has-inverse vs is-equiv) `:206`** — has-inverse(f) := Σ (g : B → A) (f ∘ g ~ id_B) × (g ∘ f ~ id_A); any invertible map is an equivalence. Equivalences are NOT defined as invertible maps: is-equiv(f) should be a property (a proposition, provable once function extensionality is available), while has-inverse(f) can be a homotopically complicated type — the text points ahead to has-inverse(id_{S¹}) ≃ ℤ for the identity map on the circle.
- **Proposition (is-equiv → has-inverse) `:225`** — any equivalence can be given the structure of an invertible map: there is a map is-equiv(f) → has-inverse(f). Given section (g, G) and retraction (h, H), the homotopy K := (H · g)⁻¹ ∙ (h · G) : g ~ h upgrades the section g to a two-sided inverse.
- **Corollary (inverse of an equivalence) `:248`** — the inverse of an equivalence is again an equivalence: the section of an equivalence f is itself invertible, with inverse f.
- **Example (laws of coproducts and products) `:256`** — the unit, commutativity, associativity, zero, and distributivity laws for + and × hold as equivalences, e.g. ∅ + B ≃ B, A + B ≃ B + A, 𝟙 × B ≃ B, A × ∅ ≃ ∅, A × (B + C) ≃ (A × B) + (A × C); all constructed by induction/pattern matching.
- **Example (laws of Σ-types) `:284`** — generalizations to Σ: absorption Σ (x:∅) B(x) ≃ ∅ ≃ Σ (x:A) ∅; unit laws Σ (x:𝟙) B(x) ≃ B(⋆) and Σ (x:A) 𝟙 ≃ A; two forms of associativity (over a family C on Σ (x:A) B(x), or a doubly indexed family C(x,y)); Σ distributes over + on both sides. Commutativity does not generalize to Σ-types.
- **Definition (Eq-Σ) `:348`** — observational equality on Σ-types: for a family B over A and s, t : Σ (x:A) B(x), Eq-Σ(s, t) := Σ (α : pr₁ s = pr₁ t) tr_B(α, pr₂ s) = pr₂ t.
- **Lemma (reflexivity of Eq-Σ) `:359`** — Eq-Σ is reflexive: refl-Eq-Σ : Π (s : Σ (x:A) B(x)) Eq-Σ(s, s), by Σ-induction, taking (refl, refl).
- **Definition (pair-eq) `:374`** — pair-eq : (s = t) → Eq-Σ(s, t), defined by path induction with pair-eq(refl_s) := refl-Eq-Σ(s).
- **Theorem (identity types of Σ-types) `:382`** — for any type family B over A and any s, t : Σ (x:A) B(x), the map pair-eq : (s = t) → Eq-Σ(s, t) is an equivalence.

#### `contractible.tex` — Contractible types and contractible maps

Develops contractible types — types with, up to identification, only one element — as singletons up to homotopy: the total space of paths out of a point is contractible, and contractibility is equivalent to pointedness plus a singleton induction principle. Then introduces the fiber of a map and contractible maps (all fibers contractible), and proves that a map is an equivalence if and only if it is contractible, with coherently invertible maps as the intermediate notion.

- **Definition (is-contr) `:22`** — a type A is contractible if it comes equipped with an element of is-contr(A) := Σ (c:A) Π (x:A) c = x; c is the center of contraction, C : Π (x:A) c = x the contraction. The contraction is judgmentally a homotopy const_c ~ id_A (`:30`). The unit type is contractible (`:38`).
- **Theorem (total space of the identity type) `:42`** — for any a : A, the type Σ (x:A) a = x is contractible, with center of contraction (a, refl_a).
- **Definition (singleton induction) `:64`** — a type A equipped with a : A satisfies singleton induction if for every type family B over A, the evaluation map ev-pt : (Π (x:A) B(x)) → B(a), f ↦ f(a), has a section: ind-sing_a : B(a) → Π (x:A) B(x) with comp-sing_a : ev-pt ∘ ind-sing_a ~ id. This is the induction principle of the unit type with the computation rule given by an identification rather than a judgmental equality (`:77`).
- **Theorem (contractibility ⟺ singleton induction) `:89`** — for any type A, the following are equivalent: (i) A is contractible; (ii) A comes equipped with an element a : A and satisfies singleton induction.
- **Definition (fiber) `:134`** — the fiber of f : A → B at b : B is fib_f(b) := Σ (a:A) f(a) = b — the type-theoretic preimage of f at b.
- **Definition (Eq-fib) `:156`** — observational equality of the fiber: for (x, p), (x', p') : fib_f(y), Eq-fib_f((x,p), (x',p')) := Σ (α : x = x') p = ap f (α) ∙ p'; it is a reflexive relation via λ(x,p). (refl, refl).
- **Proposition (identity type of a fiber) `:168`** — the canonical map ((x,p) = (x',p')) → Eq-fib_f((x,p), (x',p')) induced by reflexivity is an equivalence, for any (x,p), (x',p') : fib_f(y).
- **Definition (contractible map) `:189`** — a map f : A → B is contractible if all its fibers are contractible: is-contr(f) := Π (b:B) is-contr(fib_f(b)).
- **Theorem (contractible maps are equivalences) `:196`** — any contractible map is an equivalence: the centers of contraction of the fibers assemble into a section (g, G), and g is also a retraction.
- **Definition (coherently invertible map) `:226`** — f : A → B is coherently invertible if it comes equipped with g : B → A, G : f ∘ g ~ id, H : g ∘ f ~ id, and a further coherence homotopy K : G · f ~ f · H between the two induced homotopies of type f ∘ g ∘ f ~ f; is-coh-invertible(f) is the type of such quadruples (g, G, H, K).
- **Proposition (coherently invertible → contractible fibers) `:239`** — any coherently invertible map has contractible fibers; the fiber at y has center of contraction (g(y), G(y)).
- **Definition (naturality of homotopies) `:283`** — for f, g : A → B, H : f ~ g, and p : x = y, an identification nat-htpy(H, p) : ap f (p) ∙ H(y) = H(x) ∙ ap g (p), witnessing that the naturality square of H at p commutes.
- **Definition (retraction swap) `:306`** — for f : A → A with H : f ~ id_A, an identification H(f(x)) = ap f (H(x)) for any x : A, extracted from the naturality square.
- **Lemma (has-inverse → is-coh-invertible) `:321`** — given f equipped with an inverse (g, G : f ∘ g ~ id, H : g ∘ f ~ id), the homotopy G can be improved to G' : f ∘ g ~ id equipped with a coherence K : f · H ~ G' · f; hence there is a map has-inverse(f) → is-coh-invertible(f).
- **Theorem (equivalences are contractible maps) `:362`** — any equivalence is a contractible map: an equivalence is invertible, an invertible map is coherently invertible, and a coherently invertible map has contractible fibers.
- **Corollary (opposite total space) `:372`** — for any a : A, the type Σ (x:A) x = a is contractible — it is exactly the fiber of id_A at a.

#### `fundamental.tex` — The fundamental theorem of identity types

Establishes the main tool for characterizing identity types: a family of maps is a family of equivalences iff its total map is an equivalence, and the fundamental theorem — for a pointed family (B, b : B(a)), a family of maps f : Π (x:A) (a = x) → B(x) with f(a, refl) = b is a family of equivalences iff Σ (x:A) B(x) is contractible iff (B, b) is an identity system. Applications: the identity type of ℕ, equivalences are embeddings, disjointness of coproducts, and the structure identity principle.

- **Definition (total map) `:19`** — for a family of maps f : Π (x:A) B(x) → C(x), tot(f) : (Σ (x:A) B(x)) → Σ (x:A) C(x) is defined by (x, y) ↦ (x, f(x, y)).
- **Lemma (fibers of tot) `:31`** — for any family of maps f and any t : Σ (x:A) C(x), there is an equivalence fib_{tot(f)}(t) ≃ fib_{f(pr₁ t)}(pr₂ t).
- **Theorem (families of equivalences) `:61`** — for a family of maps f : Π (x:A) B(x) → C(x), the following are equivalent: (i) each f(x) is an equivalence (f is a family of equivalences); (ii) tot(f) : Σ (x:A) B(x) → Σ (x:A) C(x) is an equivalence.
- **Lemma (base change) `:83`** — if f : A → B is an equivalence and C is a type family over B, then σ_f(C) := λ(x, z). (f(x), z) : (Σ (x:A) C(f(x))) → Σ (y:B) C(y) is an equivalence; its fibers are equivalent to the fibers of f. The converse implication does not hold.
- **Definition + Theorem (tot over a base map) `:108`, `:120`** — for f : A → B and a family of maps g : Π (x:A) C(x) → D(f(x)) over f, define tot_f(g)(x, z) := (f(x), g(x, z)) : (Σ (x:A) C(x)) → Σ (y:B) D(y); if f is an equivalence, then g is a family of equivalences iff tot_f(g) is an equivalence.
- **Definition (unary identity system) `:152`** — an identity system on A at a : A is a type family B over A equipped with b : B(a) such that for every family P(x, y) indexed by x : A, y : B(x), the map h ↦ h(a, b) : (Π (x:A) Π (y:B(x)) P(x, y)) → P(a, b) has a section — identification elimination with the computation rule as an identification.
- **Theorem (fundamental theorem of identity types) `:181`** — let a : A, let B be a family over A with b : B(a), and consider ANY family of maps f : Π (x:A) (a = x) → B(x) equipped with an identification f(a, refl_a) = b. Then the following are equivalent: (i) f is a family of equivalences; (ii) the total space Σ (x:A) B(x) is contractible; (iii) B equipped with b is an identity system. In particular, the canonical family path-ind_a(b) : Π (x:A) (a = x) → B(x) is a family of equivalences iff Σ (x:A) B(x) is contractible. The general f (rather than only the canonical one) is deliberate: the theorem is often applied to a family that is not by definition the canonical one. The main implication in use is (ii) → (i).
- **Theorem (identity type of ℕ) `:242`** — for each m, n : ℕ, the canonical map (m = n) → Eq-ℕ(m, n) is an equivalence, where the observational equality Eq-ℕ is defined recursively by Eq-ℕ(0, 0) := 𝟙, Eq-ℕ(0, n+1) := ∅, Eq-ℕ(m+1, 0) := ∅, Eq-ℕ(m+1, n+1) := Eq-ℕ(m, n).
- **Definition (embedding) `:293`** — f : A → B is an embedding if ap_f : (x = y) → (f(x) = f(y)) is an equivalence for every x, y : A; is-emb(f) is the type of such witnesses, and A ↪ B := Σ (f : A → B) is-emb(f). Embeddings are the homotopical analogue of injective maps.
- **Theorem (equivalences are embeddings) `:306`** — any equivalence is an embedding; equivalently phrased, equivalent types have equivalent identity types.
- **Definition (Eq-coprod) `:359`** — observational equality on A + B, by double induction: Eq(inl x, inl x') := (x = x'), Eq(inl x, inr y') := ∅, Eq(inr y, inl x') := ∅, Eq(inr y, inr y') := (y = y'); it is reflexive, giving a canonical map (s = t) → Eq-coprod(s, t) (`:374`).
- **Proposition (contractibility of the total space) `:391`** — for any s : A + B, the total space Σ (t : A+B) Eq-coprod(s, t) is contractible.
- **Theorem (disjointness of coproducts) `:345`** — for any x, x' : A and y, y' : B there are equivalences (inl x = inl x') ≃ (x = x'), (inl x = inr y') ≃ ∅, (inr y = inl x') ≃ ∅, (inr y = inr y') ≃ (y = y').
- **Definition (dependent identity system) `:442`** — given an identity system C on A at a with c : C(a) and a family B over A, a dependent identity system over C at b : B(a) is a family D : Π (x:A) B(x) → (C(x) → 𝒰) with d : D(a, b, c) such that y ↦ D(a, y, c) is an identity system on B(a) at b.
- **Theorem (structure identity principle) `:450`** — given B over A, a : A, b : B(a), an identity system C with c : C(a), and D : Π (x:A) B(x) → (C(x) → 𝒰) with d : D(a, b, c), the following are equivalent: (i) any family of maps (b = y) → D(a, y, c) indexed by y : B(a) is a family of equivalences; (ii) Σ (y : B(a)) D(a, y, c) is contractible; (iii) D is a dependent identity system over C at b; (iv) any family of maps ((a, b) = (x, y)) → Σ (z : C(x)) D(x, y, z) is a family of equivalences; (v) Σ ((x,y) : Σ (x:A) B(x)) Σ (z : C(x)) D(x, y, z) is contractible; (vi) (x, y) ↦ Σ (z : C(x)) D(x, y, z) is an identity system at (a, b). Consequence: characterizing the identity type of a structure Σ-type reduces to two contractibility checks, of Σ (x:A) C(x) and Σ (y:B(a)) D(a, y, c).

#### `hierarchy.tex` — Propositions, sets, and the higher truncation levels

Builds the hierarchy of truncation levels from the bottom up: propositions are the types with
contractible identity types, sets those with propositional identity types, and in general a
(k+1)-type is one whose identity types are k-types, with contractible types at level -2. Subtypes
and embeddings are the map-level counterparts of propositions, and the section closes with the
general is-trunc hierarchy, its closure properties, and the characterization of (k+1)-truncated maps.

- **Definition (is-prop) `:24`** — a type A is a proposition if its identity types are contractible: is-prop(A) := Π(x,y:A) is-contr(x=y); Prop_𝒰 := Σ(X:𝒰) is-prop(X) is the type of small propositions.
- **Proposition (characterizations of is-prop) `:45`** — for a type A the following are equivalent: (i) A is a proposition; (ii) any two elements are equal, is-prop'(A) := Π(x,y:A) x=y; (iii) A is contractible as soon as inhabited, A → is-contr(A); (iv) the map const_⋆ : A → 1 is an embedding.
- **Proposition (equivalences between propositions) `:80`** — a map f : P → Q between propositions is an equivalence iff there is a map g : Q → P; consequently (P ≃ Q) ↔ (P ↔ Q).
- **Definition (subtype / property) `:111`** — a type family B over A is a subtype of A if each B(x) is a proposition; B(x) is then called a property of x:A. Propositions are closed under equivalence (`:134`).
- **Theorem (embeddings = propositional fibers) `:151`** — a map f : A → B is an embedding iff the fiber fib_f(b) is a proposition for each b:B; corollary `:175` — pr1 : (Σ(x:A) B(x)) → A is an embedding iff B(x) is a proposition for each x:A.
- **Definition (is-set) `:194`** — a type A is a set if its identity types are propositions: is-set(A) := Π(x,y:A) is-prop(x=y); ℕ is a set (`:202`), and A is a set iff it satisfies axiom K, Π(x:A) Π(p:x=x) refl_x = p (`:210`).
- **Theorem (set criterion) `:228`** — given a binary relation R : A → A → 𝒰 with (i) each R(x,y) a proposition, (ii) R reflexive (ρ : Π(x:A) R(x,x)), (iii) maps R(x,y) → (x=y), any family of maps Π(x,y:A) (x=y) → R(x,y) is a family of equivalences, and A is a set.
- **Theorem (Hedberg) `:261`** — any type with decidable equality (d : Π(x,y:A) (x=y) + (x≠y)) is a set.
- **Definition (is-trunc) `:312`** — by recursion on the index type 𝕋 (generated by -2 and successor): is-trunc_{-2}(A) := is-contr(A) and is-trunc_{k+1}(A) := Π(x,y:A) is-trunc_k(x=y); A is a k-type if is-trunc_k(A) holds, 𝒰^{≤k} := Σ(X:𝒰) is-trunc_k(X), and a map is k-truncated if its fibers are; truncatedness is independent of the ambient universe (`:328`).
- **Proposition (cumulativity) `:343`** — if A is a k-type then A is a (k+1)-type; hence identity types of k-types are k-types (`:354`).
- **Proposition (closure under equivalence) `:358`** — if e : A ≃ B and B is a k-type, then so is A; corollary `:372` — if f : A → B is an embedding and B is a (k+1)-type, then so is A.
- **Theorem ((k+1)-truncated maps via ap) `:386`** — a map f : A → B is (k+1)-truncated iff for each x,y:A the map ap_f : (x=y) → (f(x)=f(y)) is k-truncated; this generalizes the embedding characterization at `:151`.

#### `funext.tex` — Function extensionality

States the function extensionality axiom — the identity type f = g of dependent functions is
equivalent to the type of homotopies f ~ g — together with its equivalent forms via the fundamental
theorem of identity types and the weak function extensionality principle. It is then applied to
closure of k-types under Π, type-theoretic choice and identity systems on Π-types, the dependent
universal properties of Σ-types and identity types, precomposition by an equivalence, and the
strong induction principle of ℕ.

- **Proposition (equivalent forms at f) `:32`** — for f : Π(x:A) B(x) the following are equivalent: (i) function extensionality at f: the family htpy-eq : (f=g) → (f ~ g), defined by htpy-eq(refl_f) := refl-htpy_f, is a family of equivalences; (ii) the total space Σ(g:Π(x:A)B(x)) f ~ g is contractible; (iii) homotopy induction: for any family P(g,H) over g : Π(x:A)B(x) and H : f ~ g, evaluation s ↦ s(f, refl-htpy_f) has a section.
- **Theorem (funext ⟺ weak funext) `:63`** — in any universe 𝒰, function extensionality (htpy-eq an equivalence for all B, f, g in 𝒰) holds iff the weak function extensionality principle holds: (Π(x:A) is-contr(B(x))) → is-contr(Π(x:A) B(x)).
- **Axiom (Function Extensionality) `:111`** — for any type family B over A and any f,g : Π(x:A) B(x), the map htpy-eq : (f=g) → (f ~ g) is an equivalence; its inverse is written eq-htpy.
- **Theorem (Π of k-types) `:132`** — (Π(x:A) is-trunc_k(B(x))) → is-trunc_k(Π(x:A) B(x)); corollary `:145` — if B is a k-type then A → B is a k-type for any A; in particular ¬A is a proposition for every type A (`:149`).
- **Theorem (type-theoretic choice) `:157`** — for C(x,y) indexed by x:A and y:B(x), the map choice : (Π(x:A) Σ(y:B(x)) C(x,y)) → (Σ(f:Π(x:A)B(x)) Π(x:A) C(x,f(x))), given by h ↦ (λx.pr1(h(x)), λx.pr2(h(x))), is an equivalence.
- **Corollary (sections of pr1) `:230`** — for any family B over A, sections(pr1) ≃ Π(x:A) B(x), where pr1 : (Σ(x:A) B(x)) → A.
- **Theorem (identity systems on Π-types) `:262`** — given a family B over A with an identity system E(b) at each b : B(a), and f : Π(x:A) B(x), the family g ↦ Π(x:A) E(f(x), g(x)) over g : Π(x:A) B(x) is an identity system at f.
- **Theorem (dependent universal property of Σ-types) `:297`** — for B over A and C over Σ(x:A) B(x), the map ev-pair : (Π(z:Σ(x:A)B(x)) C(z)) → (Π(x:A) Π(y:B(x)) C(x,y)), f ↦ λx.λy.f(x,y), is an equivalence; corollary `:325` — currying (A×B → X) → (A → (B → X)) is an equivalence.
- **Theorem (dependent universal property of identity types / type-theoretic Yoneda lemma) `:350`** — for a:A and a family B(x,p) indexed by x:A and p:a=x, the map ev-refl : (Π(x:A) Π(p:a=x) B(x,p)) → B(a, refl_a), f ↦ f(a, refl_a), is an equivalence.
- **Theorem (precomposition by an equivalence) `:382`** — for f : A → B the following are equivalent: (i) f is an equivalence; (ii) for every family P over B, the map – ∘ f : (Π(y:B) P(y)) → (Π(x:A) P(f(x))) is an equivalence; (iii) for every type X, the map – ∘ f : (B → X) → (A → X) is an equivalence.
- **Theorem (strong induction for ℕ) `:468`** — given a family P over ℕ with p₀ : P(0) and p_S : Π(n:ℕ) (Π(m:ℕ) (m≤n) → P(m)) → P(n+1), there is strong-ind_ℕ(p₀,p_S) : Π(n:ℕ) P(n) satisfying the computation rules (as identifications) strong-ind_ℕ(p₀,p_S,0) = p₀ and strong-ind_ℕ(p₀,p_S,n+1) = p_S(n, λm.λp.strong-ind_ℕ(p₀,p_S,m)).

#### `propositional-truncation.tex` — Propositional truncations

Specifies when a map into a proposition is a propositional truncation — by the universal property
that precomposition into any proposition is an equivalence — and shows this determines the
truncation uniquely up to equivalence. It then constructs ∥A∥ as a higher inductive type with a
point constructor η and a path constructor α, uses it to interpret disjunction and existential
quantification, and proves Kraus's theorem extending weakly constant maps into sets along η.

- **Definition (is a propositional truncation) `:22`** — a map f : A → P into a proposition P is a propositional truncation of A if for every proposition Q the precomposition map – ∘ f : (P → Q) → (A → Q) is an equivalence; equivalently, every map g : A → Q extends uniquely along f (`:30`); since X → Q is a proposition, it suffices to give some map (A → Q) → (P → Q) for every proposition Q (`:44`).
- **Proposition (3-for-2 / uniqueness) `:56`** — for f : A → P and f' : A → P' into propositions, if any two of the following hold, so does the third: (i) f is a propositional truncation of A; (ii) f' is a propositional truncation of A; (iii) there is a (unique) equivalence P ≃ P'.
- **Remark (¬¬A is not the truncation) `:86`** — ¬¬A is a proposition with a map A → ¬¬A, and precomposition (¬¬A → ¬¬Q) → (A → ¬¬Q) is an equivalence, but only for doubly negated propositions; the general universal property is not provable, and propositional truncations are not guaranteed to exist in Martin-Löf type theory — new rules are added.
- **Lemma (∥A∥ is a proposition) `:146`** — the higher inductive type ∥A∥, with point constructor η : A → ∥A∥ and path constructor α : Π(x,y:∥A∥) x=y (formation and constructors at `:117`–`:143`), is a proposition, immediately by α.
- **Definition (induction principle of ∥A∥) `:178`** — for any family Q over ∥A∥: given f : Π(a:A) Q(η(a)) and identifications tr_Q(α(x,y), u) = v for all u : Q(x), v : Q(y), and x,y : ∥A∥, there is h : Π(t:∥A∥) Q(t) with h ∘ η ~ f; the second requirement holds iff Q is a family of propositions (`:194`).
- **Theorem (η satisfies the universal property) `:213`** — the map η : A → ∥A∥ satisfies the universal property of the propositional truncation of A; consequently ∥–∥ acts functorially, ∥–∥ : (A → B) → (∥A∥ → ∥B∥) with ∥id∥ ~ id and ∥g ∘ f∥ ~ ∥g∥ ∘ ∥f∥ (`:231`).
- **Definition (disjunction) `:263`** — for propositions P and Q, P ∨ Q := ∥P + Q∥; it carries i := η ∘ inl : P → P∨Q and j := η ∘ inr : Q → P∨Q, and satisfies (P∨Q → R) ↔ ((P → R) × (Q → R)) for any proposition R (`:270`).
- **Definition (existential quantification) `:292`** — for a family P of propositions over A, ∃_{x:A} P(x) := ∥Σ(x:A) P(x)∥; it carries Π(a:A) (P(a) → ∃_{x:A} P(x)) and satisfies ((∃_{x:A} P(x)) → Q) ↔ (Π(x:A) P(x) → Q) for any proposition Q (`:299`).
- **Remark (global choice) `:376`** — a type A satisfies the principle of global choice if there is a map ∥A∥ → A; decidable subtypes of ℕ admit such a map via the minimal element (`:348`), but univalence shows not every type does.
- **Definition (weakly constant map) `:390`** — is-weakly-constant(f) := Π(x,y:A) f(x) = f(y); any f factoring through η up to homotopy is weakly constant (`:403`).
- **Theorem (Kraus) `:424`** — for any type A and any set B, the map (∥A∥ → B) → Σ(f:A→B) Π(x,y:A) f(x) = f(y), given by g ↦ (g ∘ η, λx.λy.ap_g(α(x,y))), is an equivalence; that is, every weakly constant map into a set extends uniquely along η.

#### `images.tex` — Image factorizations

Constructs the image of a map f : A → X as an embedding
i_f : im(f) ↪ X through which f factors, built from the
propositional truncation and characterized by a universal property
among embeddings. Develops surjective maps and their dependent
universal property, yielding the unique
surjection-then-embedding factorization of any map. Closes with
Cantor's diagonal argument: no type surjects onto its power set.

- **Definition (morphism from f to g over X) `:20`** — for f : A → X and g : B → X, hom_X(f,g) := Σ(h : A → B) f ~ g∘h; composition is (k,K)∘(h,H) := (k∘h, H ∙ (K·h)).
- **Definition (universal property of the image) `:38`** — given f ~ i∘q with i : I → X an embedding, i satisfies the universal property of the image of f if precomposition –∘(q,H) : hom_X(i,m) → hom_X(f,m) is an equivalence for every embedding m : B ↪ X. Since hom_X(f,m) is a proposition whenever m is an embedding (`:54`), it suffices to give any map hom_X(f,m) → hom_X(i,m) for every embedding m (`:67`).
- **Definition (the image) `:96`** — im(f) := Σ(x:X) ‖fib_f(x)‖, with image inclusion i_f := pr₁, the map q_f : A → im(f) given by q_f(x) := (f(x), η(x, refl)), and the homotopy I_f : f ~ i_f∘q_f given by refl; i_f is an embedding because each ‖fib_f(x)‖ is a proposition (`:124`).
- **Theorem `:132`** — the image inclusion i_f : im(f) → X of any map f : A → X satisfies the universal property of the image of f.
- **Theorem (uniqueness of the image) `:157`** — for two factorizations f ~ i∘q and f ~ i'∘q' with i : B → X and i' : B' → X embeddings, consider: (i) i satisfies the universal property of the image of f; (ii) i' satisfies it; (iii) the type of equivalences e : B ≃ B' with a homotopy i ~ i'∘e is contractible. If any two of the three hold, so does the third.
- **Definition (surjective map) `:209`** — is-surj(f) := Π(b:B) ‖fib_f(b)‖.
- **Proposition (dependent universal property of surjective maps) `:226`** — for f : A → B the following are equivalent: (i) f is surjective; (ii) for every family P of propositions over B, precomposition –∘f : (Π(y:B) P(y)) → (Π(x:A) P(f(x))) is an equivalence; (iii) for every k ≥ −2 and every family P of (k+1)-truncated types over B, that precomposition map is k-truncated.
- **Theorem `:284`** — given f ~ m∘q with m an embedding: m satisfies the universal property of the image of f iff q is surjective.
- **Corollary (unique factorization) `:332`** — every map factors uniquely as a surjective map followed by an embedding: for two such factorizations (q,i), (q',i') of f, the type of (e,H) : hom_X(i,i') with e an equivalence, together with an identification (e,H)∘(q,I) = (q',I') in hom_X(f,i'), is contractible.
- **Definition (U-power set) `:356`** — P_U(X) := X → Prop_U, the type of families of propositions in a universe U indexed by X.
- **Theorem (Cantor) `:363`** — for any type X and any universe U there is no surjective function X → P_U(X); given f, the diagonal subset P(x) := ¬(f(x,x)) yields a contradiction from any merely-given preimage of P.

#### `finite-types.tex` — Finite types

Defines countings — equivalences Fin k ≃ A from a standard finite
type — and proves their closure under coproducts, Σ, and cartesian
products. Proves the double-counting theorem that Fin k ≃ Fin l
forces k = l, via injectivity of X ↦ X + 1. Then truncates:
is-finite(X) := ‖Σ(k:ℕ) Fin k ≃ X‖ is the propositional notion,
under which every finite type gets a unique cardinality, the
principle of finite choice holds, and finiteness is closed under
+, ×, and Σ.

- **Definition (countings) `:7`** — cnt(A) := Σ(k:ℕ) (Fin k ≃ A); an element (k,e) : cnt(A) says A has k elements. The type cnt(A) is often not a proposition (`:15`); any type with a counting has decidable equality (`:35`).
- **Theorem (closure of countings, thm:count) `:39`** — (i) A and B both come equipped with countings iff A + B does. (ii) For a family B over A: if A has a counting, then (each B(x) has a counting) iff (Σ(x:A) B(x) has a counting); if both of those hold and B has a section Π(x:A) B(x), then A has a counting. Consequently, for P a subtype of a type A with a counting: cnt(Σ(x:A) P(x)) ↔ Π(x:A) is-decidable(P(x)).
- **Corollary (products, cor:count-prod) `:112`** — countings on A and B give a counting on A × B; a counting on A × B gives functions B → cnt(A) and A → cnt(B).
- **Proposition (Maybe is injective, prp:is-injective-maybe) `:138`** — for any two types X and Y there is a map (X + 1 ≃ Y + 1) → (X ≃ Y).
- **Theorem (double counting, thm:is-injective-Fin) `:219`** — for any k, l : ℕ there is a map (Fin k ≃ Fin l) → (k = l).
- **Definition (finiteness, defn:finite) `:244`** — is-finite(X) := ‖Σ(k:ℕ) Fin k ≃ X‖; the type of finite types is 𝔽 := Σ(X:U₀) is-finite(X), i.e. the image of Fin : ℕ → U₀; the type of k-element types is BS_k := Σ(X:U₀) ‖Fin k ≃ X‖.
- **Theorem (cardinality) `:272`** — is-finite'(X) := Σ(k:ℕ) ‖Fin k ≃ X‖ is a proposition, and is-finite(X) ↔ is-finite'(X); for finite X the unique k with ‖Fin k ≃ X‖ is the cardinality |X|.
- **Corollary `:307`** — 𝔽 ≃ Σ(k:ℕ) BS_k.
- **Proposition (finite choice, prp:finite-choice) `:324`** — for any family B over a finite type A there is a map (Π(x:A) ‖B(x)‖) → ‖Π(x:A) B(x)‖.
- **Theorem (closure of finite types) `:346`** — (i) X and Y are both finite iff X + Y is finite. (ii) If X and Y are finite then X × Y is finite; if X × Y is finite there are functions Y → is-finite(X) and X → is-finite(Y). (iii) For a family B over A: if A is finite, then (each B(x) is finite) iff (Σ(x:A) B(x) is finite); if both of those hold, then A is finite iff A is a set and Σ(x:A) ¬B(x) is finite; and if both hold and B has a section, then A is finite.

#### `univalence.tex` — The univalence axiom

Characterizes the identity type of a universe: univalence asserts
that equiv-eq : (A = B) → (A ≃ B) is an equivalence, and by the
fundamental theorem of identity types this comes in three
equivalent forms, including equivalence induction. From it the
lecture derives propositional extensionality, Voevodsky's theorem
that univalence implies function extensionality, and the object
and subtype classifiers. It then shows global choice and global
decidability are incompatible with univalence — the axiom of
choice and excluded middle must be stated for sets and
propositions — and constructs the binomial types.

- **Theorem (three equivalent forms) `:14`** — for a universe U the following are equivalent: (i) U is univalent: for all A, B : U the map equiv-eq : (A = B) → (A ≃ B), defined by equiv-eq(refl) := id, is an equivalence; (ii) Σ(B:U) A ≃ B is contractible for each A : U; (iii) equivalence induction: for every A : U and family P(X,e) indexed by X : U and e : A ≃ X, the map (Π(X:U) Π(e:A≃X) P(X,e)) → P(A,id), f ↦ f(A,id), has a section.
- **Axiom (univalence) `:49`** — all the universes generated by the enough-universes postulate are assumed univalent; for a univalent universe U, eq-equiv denotes the inverse of equiv-eq.
- **Theorem (propositional extensionality) `:143`** — for any two propositions P and Q, the canonical map iff-eq : (P = Q) → (P ↔ Q), iff-eq(refl) := (id,id), is an equivalence; consequently Prop_U is a set. (Via the subuniverse form of univalence `:117`: for a family P of propositions over U, (A = B) ≃ (pr₁A ≃ pr₁B) in Σ(X:U) P(X).)
- **Lemma (postcomposition) `:180`** — for any equivalence e : X ≃ Y in a univalent universe U and any type A, postcomposition e∘– : (A → X) → (A → Y) is an equivalence. The source proves this by equivalence induction rather than by function extensionality, since funext is what is about to be derived.
- **Theorem (univalence implies funext, Voevodsky) `:198`** — for any universe U, the univalence axiom on U implies function extensionality on U; the proof goes through weak function extensionality (every family of contractible types has contractible product).
- **Theorem (object classifier) `:249`** — for any type A and univalent universe U containing A, the map (Σ(X:U) X → A) → (A → U) given by (X,f) ↦ fib_f is an equivalence, with inverse B ↦ (Σ(x:A) B(x), pr₁).
- **Theorem (subuniverse classifier) `:295`** — for A in a univalent universe U and any family P over U, writing U_P := Σ(X:U) P(X), the map (Σ(X:U) Σ(f:X→A) Π(a:A) P(fib_f(a))) → (A → U_P) given by (X,f,p) ↦ λa.(fib_f(a), p(a)) is an equivalence. This applies to any subuniverse (k-types, decidable propositions, finite types) and also to non-propositional P such as is-decidable and cnt (`:317`).
- **Corollary (subtypes are embeddings) `:319`** — for A in a univalent universe U, the map (Σ(X:U) X ↪ A) → (A → Prop_U), (X,f) ↦ fib_f, is an equivalence: a subtype of A is equivalently a type X with an embedding X ↪ A.
- **Corollary (no global choice) `:395`** — for a univalent universe U there is no function Π(A:U) ‖A‖ → A. The counterexample lives in the 2-element types: Σ(X:BS₂) X is contractible (`:349`), so a section Π(X:BS₂) X would force BS₂ to be contractible (`:378`), which it is not; restricting a global choice function to BS₂ produces exactly such a section.

#### `set-quotients.tex` — Set quotients

Constructs the quotient A/R of a type by a prop-valued equivalence relation
as the type of equivalence classes — the image of R : A → (A → Prop_U) —
and characterizes its identity type via propositional extensionality. The
replacement axiom keeps the quotient U-small; the universal property is
proved equivalent to surjective-plus-effective and to the image
factorization of R, and the machinery is applied to partitions, choices of
unique representatives (the rationals), and set truncation.

- **Definition (equivalence relation) `:16`** — a relation R : A → (A → Prop_U) valued in propositions in U, equipped with ρ : Π(x:A) R(x,x), σ : Π(x,y:A) R(x,y) → R(y,x), and τ : Π(x,y,z:A) R(x,y) → (R(y,z) → R(x,z)); Eq-Rel_U(A) is the type of all such.
- **Definition (equivalence class; the quotient A/R) `:26`** — P : A → Prop_U is an equivalence class if ∃(x:A) ∀(y:A) P(y) ↔ R(x,y); A/R := Σ(P : A → Prop_U) is-equivalence-class(P); the class of x is [x]_R := R(x), giving the quotient map q_R : A → A/R, x ↦ [x]_R.
- **Proposition (identity type of A/R) `:48`** — for x : A and any equivalence class P, the canonical map ([x]_R = P) → P(x) is an equivalence (the characterization uses propositional extensionality).
- **Corollary (effectivity of q_R) `:76`** — ([x]_R = [y]_R) ≃ R(x,y) for all x,y : A.
- **Definition (locally U-small) `:97`** — a type A is locally U-small if the identity type x = y is U-small for every x,y : A; a map is locally U-small if all its fibers are. By univalence, any univalent universe U is locally U-small.
- **Axiom (replacement) `:122`** — for any map f : A → B from a U-small type A into a locally U-small type B, the image of f is U-small. In particular A/R is U-small when A and R are in U.
- **Definition (universal property of the set quotient) `:159`** — a map q : A → B into a set B with R(x,y) → (q(x) = q(y)) is a set quotient of R if for every set X the map q* : (B → X) → Σ(f : A → X) Π(x,y:A) R(x,y) → (f(x) = f(y)), given by h ↦ (h ∘ q, λx.λy.λr. ap_h(H(r))), is an equivalence — every R-invariant map into a set extends uniquely along q. The source stresses that the universal property is formulated with respect to sets.
- **Theorem (three characterizations of set quotients) `:189`** — for R a U-valued equivalence relation on A and q : A → B a map into a set B (not necessarily in U), the following are equivalent: (i) q identifies R-related elements and satisfies the universal property of the set quotient; (ii) q is surjective and effective, i.e. (q(x) = q(y)) ≃ R(x,y) for all x,y; (iii) R extends along q to an embedding i : B → Prop_U^A satisfying the universal property of the image inclusion of R.
- **Theorem (equivalence relations ≃ surjections into sets) `:350`** — Eq-Rel_U(A) ≃ Σ(X : Set_U) A ↠ X; forward by the replacement-resized quotient A/R, backward by K_f(x,y) := (f(x) = f(y)).
- **Theorem (unique representatives give the quotient) `:499`** — if C is a choice of representatives for R, i.e. Π(x:A) is-contr(Σ(y:A) C(y) × R(x,y)) with center (h(x), c(x), r(x)), then q : A → Σ(x:A) C(x), q(x) := (h(x), c(x)), is a map into a set with q(x) = q(y) whenever R(x,y), satisfying the universal property of the set quotient — with the universe level kept low without replacement. Applications: ℕ → Fin(k+1) quotients the mod-(k+1) congruence; ℚ is defined as the reduced fractions Σ((x,y):Q) (y > 0) ∧ (gcd(x,y) = 1).
- **Definition (set truncation) `:622`** — a map f : A → B into a set B is a set truncation if precomposition − ∘ f : (B → X) → (A → X) is an equivalence for every set X.
- **Theorem (characterizations of set truncation) `:632`** — for f : A → B into a set B, the following are equivalent: (i) f is a set truncation; (ii) f satisfies the dependent universal property: − ∘ f : (Π(b:B) X(b)) → (Π(a:A) X(f(a))) is an equivalence for every family X of sets over B; (iii) f is surjective and effective with respect to x,y ↦ ‖x = y‖, i.e. (f(x) = f(y)) ≃ ‖x = y‖. Consequently every A : U has a set truncation η : A → ‖A‖₀ with ‖A‖₀ in U (via replacement), and a map into a set is a set truncation iff it is connected (`:714`).

#### `groups.tex` — Groups in univalent mathematics

Introduces groups by first defining the type of all semigroups and then
carving out groups as a subtype (unitality and having inverses are
propositions), proves that isomorphic (semi)groups are equal via the
fundamental theorem of identity types and the structure identity
principle, constructs the homotopy groups π_n as set-truncated iterated
loop spaces, proves them abelian for n ≥ 2 by the Eckmann–Hilton
argument, and closes with the concrete-versus-abstract perspective:
every group is the loop space of a unique pointed connected 1-type BG.

- **Definition (semigroup) `:22`** — a triple (G, μ, α): a set G in U, a binary operation μ : G → (G → G), and α : Π(x,y,z:G) μ(μ(x,y),z) = μ(x,μ(y,z)); Semigroup_U := Σ(G : Set_U) Σ(μ) associativity.
- **Lemma (is-unital is a proposition) `:48`** — is-unital(G), the type of triples (e, left-unit, right-unit) with e : G, left-unit : Π(y) μ(e,y) = y, right-unit : Π(x) μ(x,e) = x, is a proposition for any semigroup G — being unital is a property; Monoid_U := Σ(G : Semigroup_U) is-unital(G).
- **Definition (group) `:59`** — a unital semigroup G has inverses if equipped with x ↦ x⁻¹ : G → G satisfying left-inv : Π(x) μ(x⁻¹,x) = e and right-inv : Π(x) μ(x,x⁻¹) = e; is-group(G) := Σ(e : is-unital(G)) is-group'(G,e); a group is a unital semigroup with inverses, and is-group(G) is a proposition (`:72`).
- **Definition (group homomorphism) `:109`** — hom(G,H) is the type of pairs (f, μ_f) with f : G → H and μ_f : Π(x,y:G) f(μ_G(x,y)) = μ_H(f(x), f(y)); equality of homomorphisms is equivalent to homotopy of underlying maps, so hom(G,H) is a set (`:121`).
- **Definition (isomorphism) `:146`** — h : hom(G,H) is an iso if equipped with (h⁻¹, p, q): a homomorphism h⁻¹ : hom(H,G) with identifications p : h⁻¹ ∘ h = id_G and q : h ∘ h⁻¹ = id_H; (G ≅ H) := Σ(h : hom(G,H)) Σ(k : hom(H,G)) (k ∘ h = id) × (h ∘ k = id); is-iso(h) is a proposition, so G ≅ H is a set (`:159`).
- **Lemma (lem:grp_iso) `:178`** — a (semi)group homomorphism is an isomorphism iff its underlying map is an equivalence; consequently (G ≅ H) ≃ Σ(e : G ≃ H) Π(x,y:G) e(μ_G(x,y)) = μ_H(e(x), e(y)).
- **Theorem (iso-eq for semigroups) `:202`** — for a semigroup G in a univalent universe U, iso-eq : (G = H) → (G ≅ H), refl ↦ id, is a family of equivalences indexed by H : Semigroup_U (by the fundamental theorem of identity types and the structure identity principle); hence Semigroup_U is a 1-type (`:226`).
- **Theorem (isomorphic groups are equal) `:244`** — for groups G, H in a univalent universe, iso-eq : (G = H) → (G ≅ H) is an equivalence; the proof factors through ap of the projection Group_U → Semigroup_U, which is an embedding since being a group is a property, and applies 3-for-2. The type of groups is a 1-type (`:263`).
- **Definition (loop space, iterated loop space) `:283`** — on pointed types U_* := Σ(X:U) X, the loop space operation is Ω(A,a) := (a = a, refl); iterated: Ω⁰A := A, Ω^(n+1)A := Ω(Ω^n A).
- **Definition (homotopy groups) `:301`** — for a pointed type A and n ≥ 1, π_n(A) := ‖Ω^n A‖₀, with unit η(refl) and the unique group operation satisfying η(r)η(s) = η(r ∙ s); π₁(A) is the fundamental group. For n = 0, π₀(A) := ‖A‖₀ is only a set. π_(n+1)(A) ≅ π_n(ΩA) (`:321`), and pointed maps act functorially, sending pointed equivalences to isomorphisms (`:368`).
- **Theorem (Eckmann–Hilton) `:477`** — for any pointed type A and r,s : Ω²A there is an identification r ∙ s = s ∙ r, proved via the unit laws and the interchange law for horizontal and vertical concatenation (`:455`); hence π_n(A) is abelian for all n ≥ 2 (`:500`).
- **Theorem (truncated fundamental theorem, thm:truncated-fundamental) `:580`** — for a connected type A with a : A and a family B over A, the following are equivalent: (i) every family of maps f : Π(x:A) (a = x) → B(x) is a family of k-truncated maps; (ii) the total space Σ(x:A) B(x) is (k+1)-truncated. The source uses it to justify calling a concrete G-set X free when its type of orbits Σ(u:BG) X(u) is a set.

#### `W-types.tex` — General inductive types

Develops general inductive types as W-types W(A,B) of well-founded
trees, with a type A of constructor symbols and a family B of arities:
construction and induction principle, observational equality
characterizing the identity type and preserving truncation levels,
functorial action, the elementhood relation with its well-founded
induction principle, extensionality (characterized by univalence of the
family B), and the multiset model M_U := W(U, Ty), culminating in
Russell's paradox: a univalent universe is not small in itself.

- **Definition (W-type) `:12`** — W(A,B), for a family B over A, is the inductive type with constructor tree : Π(x:A) (B(x) → W(A,B)) → W(A,B); induction: for any family P over W(A,B), any h : Π(x:A) Π(α : B(x) → W(A,B)) (Π(y:B(x)) P(α(y))) → P(tree(x,α)) determines ind_W(h) : Π(x : W(A,B)) P(x) with the judgmental computation rule ind_W(h, tree(x,α)) ≐ h(x, α, λy. ind_W(h, α(y))). The source notes some authors write sup for the constructor, but that tree(a,α) does not satisfy the defining properties of a supremum (`:32`).
- **Definition (observational equality Eq_W) `:197`** — for A and each B(x) in U, the relation Eq_W : W(A,B) → W(A,B) → U is defined recursively by Eq_W(tree(x,α), tree(y,β)) := Σ(p : x = y) Π(z : B(x)) α(z) = β(tr_B(p,z)).
- **Theorem (Eq_W characterizes the identity type) `:208`** — Eq_W is reflexive and the canonical map (x = y) → Eq_W(x,y) is an equivalence for each x,y : W(A,B).
- **Theorem (truncation levels) `:240`** — for any truncation level k, if A is a (k+1)-type then so is W(A,B).
- **Definition (functorial action) `:259`** — given a map f : A' → A and a family of equivalences e_x : B'(x) ≃ B(f(x)) indexed by x : A', the map W(f,e) : W(A',B') → W(A,B) is defined inductively by W(f,e)(tree(x,α)) := tree(f(x), W(f,e) ∘ α ∘ e_x⁻¹).
- **Theorem (truncated maps are preserved) `:301`** — if f is k-truncated then so is W(f,e); in particular, if f is an equivalence or an embedding then so is W(f,e). The proof uses the fiber decomposition fib_{W(f,e)}(tree(x,α)) ≃ fib_f(x) × Π(b:B(x)) fib_{W(f,e)}(α(b)) (`:270`).
- **Definition (elementhood relation) `:330`** — for a universe U containing A and each B(x), the type-valued relation ∈ : W(A,B) → W(A,B) → U is defined by (x ∈ tree(a,α)) := Σ(y : B(a)) α(y) = x.
- **Theorem (well-founded induction) `:340`** — for any family P over W(A,B) there is a function i : (Π(x : W(A,B)) (Π(y : W(A,B)) (y ∈ x) → P(y)) → P(x)) → Π(x : W(A,B)) P(x) equipped with an identification i(h,x) = h(x, λy.λe. i(h,y)) — the induction principle restated over ∈, with a propositional computation rule.
- **Definition (extensional W-type) `:419`** — W(A,B) is extensional if the canonical map (x = y) → Π(z : W(A,B)) (z ∈ x) ≃ (z ∈ y) is an equivalence.
- **Theorem (characterization of extensionality) `:429`** — for an inhabited W-type W(A,B), the following are equivalent: (i) W(A,B) is extensional; (ii) the family B is univalent, i.e. tr_B : (x = y) → (B(x) ≃ B(y)) is an equivalence for every x,y : A — equivalently, B : A → U is an embedding (`:441`). Empty W-types are vacuously extensional, so inhabitedness is needed.
- **Definition (multisets) `:502`** — M_U := W(U, Ty) for the universal family Ty over U; {f(x) | x : A} denotes the multiset tree(A, f), with cardinality A and elements f(x); elementhood becomes (X ∈ {g(y) | y : B}) ≐ Σ(y : B) g(y) = X, and M_U is extensional by univalence (`:527`). A multiset {f(x) | x : A} in V is U-small if A is U-small and each f(x) is U-small (`:535`).
- **Theorem (Russell's paradox) `:693`** — a univalent universe U cannot be U-small: if it were, the multiset R := {i(X) | X : M_U, H : X ∉ X} in U⁺ is U-small (via the U-smallness of the universal tree Y := {i(X) | X : M_U} (`:677`) and of the elementhood types (`:566`)), and using that the inclusion i of U-small multisets is an embedding (`:606`) one derives R ∈ R ≃ R ∉ R, contradicting that no type is logically equivalent to its own negation.

### Part III — The circle

Ambient axioms: function extensionality is assumed from
`funext.tex:109` onward; univalence where named.

#### `circle.tex` — The circle

Introduces the circle S¹, the book's first higher inductive type, generated by a point base : S¹ and a path constructor loop : base = base. Any section f of a family P over S¹ acts on the generators via (f(base), apd_f(loop)), packaged as the dependent action on generators dgen_{S¹} (`:26`); the induction principle provides a section of this map, and the dependent universal property upgrades it to an equivalence (Π (x:S¹) P(x)) ≃ Σ (u : P(base)) tr_P(loop, u) = u (`:102`). The non-dependent universal property follows: maps S¹ → X correspond to free loops Σ (x:X) x = x (`:181`), with a contractibility formulation for the maps realizing a given loop (`:228`). The lecture closes by constructing an H-space structure on the circle — a multiplication mul_{S¹} with left and right unit laws and a coherence identifying the two at base (`:284`).

- **Definition (the circle and its induction principle) `:40`** — S¹ comes equipped with base : S¹ and loop : base = base, and satisfies the induction principle of the circle: for each type family P over S¹ there is a map ind_{S¹} : (Σ (u : P(base)) tr_P(loop, u) = u) → Π (x:S¹) P(x) together with a homotopy comp_{S¹} : dgen_{S¹} ∘ ind_{S¹} ~ id for the computation rules, i.e. ind_{S¹} is a section of the dependent action on generators.

#### `circle-universal-cover.tex` — The universal cover of the circle

Uses the univalence axiom to compute the loop space of the circle. Univalence turns small type families over S¹ into descent data — pairs (X, e : X ≃ X) — from which the family D(X, e) : S¹ → 𝒰 is reconstructed (`:18`); the universal cover is E := D(ℤ, succℤ) (`:71`), pictured as the helix, with the segment identifications (base, k_E) = (base, succℤ(k)_E) in its total space (`:84`). Working with descent data shows that sections of a family are equivalently fixed points of its automorphism (`:145`), and that families of maps out of E are equivalently succℤ/e-equivariant maps ℤ → X (`:209`). The (dependent) universal property of ℤ — ℤ is the initial type equipped with a point and an automorphism (`:246`, `:297`) — then supplies exactly the equivalences needed for the two closing theorems below. The lecture records that this computation of π₁(S¹) was originally discovered by Shulman, and that it led to the encode-decode method presented earlier as the fundamental theorem of identity types.

- **Theorem (the universal cover is an identity system) `:377`** — the universal cover E is an identity system at base : S¹, so (base = t) ≃ E(t) for all t : S¹; in particular Ω(S¹) = (base = base) ≃ ℤ, and since E is a family of sets the circle is a 1-type and not a 0-type (`:397`).
- **Theorem (the fundamental group of the circle) `:446`** — there is a group isomorphism π₁(S¹) ≅ ℤ: since S¹ is a 1-type, π₁(S¹) ≅ Ω(S¹), and the family of equivalences α : Π (t:S¹) (base = t) → E(t) with α(refl) := 0_E is shown, via the fundamental theorem of identity types augmented with a binary operation (`:417`), to satisfy α(p ∙ q)_ℤ = α(p)_ℤ + α(q)_ℤ.

## What the source establishes

A self-contained development of dependent type theory and univalent
foundations from first principles: the identity type and path
induction; equivalences and the fundamental theorem; the h-level
hierarchy; function extensionality, propositional truncation, and
the univalence axiom; and a first higher inductive type (the
circle) with the ℤ computation of its loop space. It fixes the
standard vocabulary and proof idioms of univalent mathematics —
`is-contr`/`is-prop`/`is-set`, `is-equiv` via contractible fibers,
transport and `ap`, the fundamental theorem of identity types — so
a development can cite the standard definition rather than restate
it. Everything recorded here is the source's own content, stated in
its own terms; every mathematical claim is CONJECTURED until
machine-checked.
