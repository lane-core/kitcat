# Agda/Cubical Agda Style Guide

This style guide documents conventions for writing Agda code, particularly in a
Cubical Agda setting. These patterns promote consistency, readability, and
maintainability.

## 1. Code Formatting

### Line Width

- **Prose**: Keep to 72 characters
- **Code**: Keep to 85 characters

Configure your editor with vertical rulers at columns 72 and 85.

### Indentation

**Use two spaces of indentation, never alignment-based indentation** — except
for multi-line type signatures, where arrows align with the colon (see below).

This applies universally: laid-out syntax, continuation lines, and nested
constructs should each add a "step" (two spaces) of indentation.

```agda
-- Always:
foo =
  let
    x = 1
  in x

-- Never (alignment-based):
foo =
  let x = 1
   in x

foo = let x = 1
       in x
```

### Binary Operators

When broken over multiple lines, binary operators (including `$`) **should**
be on the *start* of continuing lines (leading), not at the end of the line
above (trailing).

```agda
-- Always (leading operators):
result = C.subst-is-invertible (R.expand (L.expand factors))
  $ R.F-map-invertible
  $ is-reflective→left-unit-is-iso L⊣R reflective

-- Never (trailing operators):
result =
  C.subst-is-invertible (R.expand (L.expand factors)) $
  R.F-map-invertible $
  is-reflective→left-unit-is-iso L⊣R reflective
```

Exception: On the first line, `$` may be trailing to introduce a proof chain:

```agda
-- Permissible:
∘∙-assoc (f , f') (g , g') (h , h') = funext∙ (λ _ → refl) $
  ap (f ∘ g) h' ∙ ap f g' ∙ f'   ≡⟨ ∙-assoc _ _ _ ⟩
  (ap (f ∘ g) h' ∙ ap f g') ∙ f' ∎
```

### Type Signatures

If a type signature needs multiple lines, the colon and type **must** start on
the next line, indented one step. Arrows in continuing lines **must** be aligned
with the colon. This convention (from 1lab) dramatically improves readability
for complex signatures.

```agda
-- Always:
Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : x ≡ z) (r : y ≡ z)
  → Type ℓ

-- Never (alignment-based):
Triangle : ∀ {ℓ} {A : Type ℓ} {x y z : A}
         → (p : x ≡ y) (q : x ≡ z) (r : y ≡ z)
         → Type ℓ

-- Never (arrows not aligned with colon):
Triangle : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : x ≡ z) (r : y ≡ z)
  → Type ℓ
```

Binders may be broken across lines with or without arrows. Without arrows,
indent another step to align with preceding binders:

```agda
-- Okay (binders on next line aligned):
Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : x ≡ z)
    (r : y ≡ z)
  → Type ℓ
```

### Function Definitions

The RHS of a clause should generally be on the same line as the LHS.

If the RHS is an application, include the head function and as many arguments
as possible on the LHS line. Continuing arguments indent one step:

```agda
-- Prefer (head on same line):
RL[e]-invertible : C.is-invertible (R.₁ (L.₁ e))
RL[e]-invertible = C.strong-mono+epi→invertible
  RL[e]-strong-mono
  RL[e]-epic

-- Over (early break):
RL[e]-invertible : C.is-invertible (R.₁ (L.₁ e))
RL[e]-invertible =
  C.strong-mono+epi→invertible
    RL[e]-strong-mono
    RL[e]-epic
```

If a continuing line has its own arguments, indent them farther (two steps
from the clause):

```agda
unit-strong-mono = C.strong-mono-cancell (R.₁ (L.₁ f)) (η x)
  $ C.subst-is-strong-mono (unit.is-natural _ _ _)
  $ C.strong-mono-∘ (η (R.₀ a)) f
      (C.invertible→strong-mono
        (is-reflective→unit-right-is-iso L⊣R reflective))
      f-strong-mono
```

### Where Clauses

If the RHS is a single line, attach `where` on that line, with declarations
indented one step:

```agda
-- Always:
foo = {! code !} where
  bar = ...

-- Never (early break):
foo = {! code !}
  where
    bar = ...
```

If the RHS has continuation lines, `where` goes on its own continuation line,
with declarations indented two steps from the function:

```agda
foo =
  {! long code !}
  $ {! continuation !}
  where
    bar = ...
```

Same-line declarations are allowed when short:

```agda
foo = short where bar = 123
```

**Avoid wildcard types**: Provide explicit types for `where` helpers unless
unification is completely trivial. `helper : _` obscures intent and can mask
unification failures.

### Equational Reasoning

Proofs by equational reasoning should start on a new line, indented one step.

Style 1: Equations to the right, with `≡⟨` aligned:

```agda
proof =
  some expression ≡⟨ a proof ⟩
  some other term ≡⟨ other proof ⟩
  the final term  ∎
```

Style 2: For very long expressions, equations between expressions:

```agda
proof =
  some long expression
    ≡⟨ a proof ⟩
  some other long term
    ≡⟨ other proof ⟩
  the final term
    ∎
```

### Pattern/Copattern Definitions

Maintain vertical alignment between corresponding arguments and `=` signs
when lengths are similar:

```agda
-- Prefer (aligned):
max zero    zero    = zero
max zero    (suc n) = suc n
max (suc n) zero    = suc n
max (suc n) (suc k) = suc k

-- Over (unaligned):
max zero zero = zero
max zero (suc n) = suc n
max (suc n) zero = suc n
max (suc n) (suc k) = suc k
```

Skip alignment if pattern lengths differ greatly or if a clause spans
multiple lines.

### Record/Data Constructor Formatting

Choose field/constructor names to encourage vertical alignment at use sites.

In sequences of single-line fields/constructors, align type signatures by
inserting whitespace before the colon:

```agda
-- Return types aligned:
data Nf where
  lam  : Nf (Γ , τ) σ       → Nf Γ (τ `⇒ σ)
  pair : Nf Γ τ → Nf Γ σ    → Nf Γ (τ `× σ)
  unit :                      Nf Γ `⊤
  ne   : ∀ {x} → Ne Γ (` x) → Nf Γ (` x)

-- Or order by line length (monotonic):
data Nf where
  unit : Nf Γ `⊤
  lam  : Nf (Γ , τ) σ → Nf Γ (τ `⇒ σ)
  pair : Nf Γ τ → Nf Γ σ → Nf Γ (τ `× σ)
  ne   : ∀ {x} → Ne Γ (` x) → Nf Γ (` x)
```

## 2. Naming Conventions

### General Style

Use `kebab-case` as the default naming convention.

### Generic Algebraic Identifiers

Use **noun-adjective order**: `{noun}{adjective}` not `{adjective}{noun}`.

| Generic | Meaning                    | Left/Right Laws   |
|---------|----------------------------|-------------------|
| `eqv`   | reflexivity/identity       | `eqvl`, `eqvr`    |
| `inv`   | inversion/symmetry         | `invl`, `invr`    |
| `cat`   | concatenation/transitivity | `catl`, `catr`    |

Law naming pattern: `{trait-prefix}{generic}{side}`

Examples:
- Path groupoid: `eqvl : p ∙ refl ≡ p`, `invl : sym p ∙ p ≡ refl`
- Monoid: `meqvl : mempty <> x ≡ x`, `meqvr : x <> mempty ≡ x`
- Group: `ginvl : ginv x <> x ≡ mempty`, `ginvr : x <> ginv x ≡ mempty`

This convention applies across `Core.Kan` (path laws), `Core.Homotopy` (homotopy
laws), and `Core.Trait.*` (algebraic structure laws).

### Departures from Rijke

| Rijke       | Kitcat              | Rationale                              |
|-------------|---------------------|----------------------------------------|
| `inv`       | `sym`               | Avoids conflict with `htpy.inv`        |
| `concat`    | `_∙_`               | Standard cubical operator              |
| `tr`        | `transport`/`subst` | Explicit over cryptic                  |
| `iscontr`   | `is-contr`          | Kebab-case per style guide             |
| `isprop`    | `is-prop`           | Same                                   |
| `isset`     | `is-set`            | Same                                   |
| `left-unit` | `eqvl`              | Noun-adjective order                   |
| `right-unit`| `eqvr`              | Same                                   |
| `left-inv`  | `invl`              | Noun-adjective order                   |
| `right-inv` | `invr`              | Same                                   |

Preserved from Rijke: `refl`, `ap`, `apd`, `_~_`, `≃`, `is-equiv`

### Pattern Synonyms

`Z` and `S` are pattern synonyms for `zero` and `suc` (defined in `Core.Type.Nat`).

### CamelCase Exceptions

Two categories of identifiers use `camelCase` instead of `kebab-case`:

**1. Trait record names and fields** — Following Idris2 Prelude conventions:

```agda
record Trunc {ℓ} (T : Type ℓ) (n : Nat) : Type ℓ where
  field has-trunc : is-hlevel n T

record Num {u} (A : Type u) : Typeω where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    fromInteger : Int → A
```

This distinguishes trait automation from mathematical definitions. Instance names
still use `kebab-case` with the trait name: `Trunc-Π`, `Num-Nat`.

**2. Primitive/builtin identifiers** — Following Agda conventions:

```agda
primHComp, primTransp, primINeg, primIMax, primIMin
putStrLn, getLine, readFile
```

Primitives use `camelCase` (often with a `prim` prefix) to match Agda's builtin
naming and to visually distinguish low-level primitives from library code.

### Symbol Separators

Replace words with symbols where appropriate:

| Word/Phrase | Symbol |
|-------------|--------|
| "to", "implies" | `→` |
| "equivalent to" | `≃` |
| "equal to" | `≡` |

Examples: `is-equiv→is-embedding`, `Ωⁿ≃Sⁿ-map`, `PathP≡Path`

### Conversion Primitives

Fundamental type-conversion functions use compressed naming without hyphens:
`eqvtofun`, `idtofun`, `pathtofun`, `eqvtoinv`. This distinguishes core
coercion primitives from derived operations.

### Predicates and Propositions

Names of propositions should start with `is-`: `is-equiv`, `is-group-hom`

Names of more general types should start uppercase: `Group-on`, `Glue`

In theorems, the predicate appears after the thing it applies to:
`Nat-is-set`, not `is-set-Nat`.

Omit the object name if universally quantified:
`is-equiv→is-embedding`, not `f-is-equiv→f-is-embedding`

Record fields whose type is proposition-valued use `has-is-` prefix:
`has-is-set`

### Record Types

Record names follow two conventions based on purpose:

- **Structure records**: Capitalize first letter, kebab-case remainder
  - Examples: `Pullback`, `Rx-graph`, `Contravariant-lens`

- **Predicate/property records**: Lowercase with `is-`/`has-` prefix
  - Examples: `is-equiv`, `is-embedding`, `has-section`, `is-connected`

This aligns with the Predicates and Propositions convention — records bundling
properties use lowercase prefixes, while structures use capitalized names.

### Duality Naming

For dual concepts:

- The "concrete dual" should be a single word: `Coproduct`
- The categorical dual uses `co-` as a prefix: `co-product`

Hence: `is-coproduct→is-co-product`

### Displayed/Dependent Versions

The displayed version of a `Thing` may be called `ThingP`, following the
pattern of `PathP` and `SquareP`.

### Variables and Parameters

- Generalizable variables are encouraged for cleaning up long telescopes
- Do not export generalizable variables
- Explicitly annotate binders when instance search involves indeterminate types

**Naming conventions:**

```agda
u v w : Level       -- Universe levels
i j k : I           -- Interval variables
m n : Nat           -- Natural numbers
x y z : A           -- Generic elements
```

### Instance Arguments

Use instance arguments judiciously for convenience:

```agda
-- For canonical elements
instance
  tt' : ∀ {ℓ} → 𝟙 {ℓ}
  tt' = ✶

-- For derivable inequalities
instance
  0< : ∀ {n} → Z < S n
  0< = s≤s 0≤
```

**Guidelines:**
- Keep instance search predictable
- Avoid ambiguous overlapping instances
- Document when instance resolution is subtle

## 3. Module Organization

### Namespace Structure

For types with substantial implementations, organize modules in a hierarchical
namespace structure. This provides fine-grained control over public/private
visibility, consistent organization across the library, and principled
avoidance of circular dependencies.

**Directory layout for type `Ty`:**

```
Ty/
├── Type.lagda.md      (optional: raw type definition only)
├── Base.lagda.md      (basic operations, no proofs)
├── <Op>.lagda.md      (proofs about operation <Op>)
├── <Op>/              (optional: subhierarchy for complex operations)
│   ├── Base.lagda.md
│   └── Properties.lagda.md
├── Trait/
│   └── <Trait>.lagda.md   (trait instances)
└── Properties.lagda.md    (aggregates all properties)
Ty.lagda.md            (aggregator in parent namespace)
```

**Module responsibilities:**

| Module | Purpose | Allowed Imports |
|--------|---------|-----------------|
| `Ty/Type` | Raw type definition (builtins/primitives) | `Core.Type`, `Core.Base` only |
| `Ty/Base` | Basic operations (no proofs) | `Ty.Type` + external modules, NOT siblings |
| `Ty/<Op>` | Proofs about operation `<Op>` | `Ty.Type`, `Ty.Base`, external modules |
| `Ty/Trait/<Trait>` | Trait instance | As needed; only instance is public |
| `Ty/Properties` | Aggregates properties | All `Ty/*` modules |

**Trait modules**: Only the instance itself should be exported; all helper
definitions should be private.

**Properties aggregation**: For small namespaces, `Properties.lagda.md`
contains properties directly. For larger namespaces, it re-exports from
`<Op>/Properties.lagda.md` modules, with each operation's properties in a
named submodule:

```agda
module add where
  open import Ty.Add.Properties public

module mul where
  open import Ty.Mul.Properties public
```

**Aggregator module (`Ty.lagda.md`)**: Lives in the parent namespace and
controls the public API. Structure:

```agda
-- Top-level: type + constructors + instances (global identifier space)
open import Ty.Type public
open import Ty.Trait.Eq public
open import Ty.Trait.Ord public

-- Namespaced: operations and properties
module Ty where
  open import Ty.Base public
  open import Ty.Properties public
```

This gives users `Ty` and its constructors at top level, while operations
and properties are accessed as `Ty.op` and `Ty.op.property`. For example,
importing `Nat` provides `Nat`, `zero`, `suc` at top level, while
`Nat.add.assoc` accesses the associativity lemma for addition.

**Rationale**: This structure ensures:
- Minimal imports for modules that only need the type
- Clear separation between operations (functions) and properties (proofs)
- Consistent access patterns across the library (`Ty.op.property`)
- No circular dependencies (strict layering)

**Reference implementation**: The `Nat` namespace follows this format.

### Import Ordering

Imports should be grouped by the first component of the module name, with
groups sorted alphabetically.

Within groups, sort modules by length (longest first).

Order statement types: `open import`, then `import`, then `open`.

### Private Declarations

Declare private variables at the top of the module.

Use `private` blocks for internal helpers.

### Module Aliases

Use private module aliases for namespace management:

```agda
private
  module C = Cat.Reasoning C
```

Instantiated module aliases must not be exported from parametrised anonymous
modules.

### Anonymous Modules for Parameter Sharing

Use `module _` to share parameters across related definitions:

```agda
module _ {A : Type} (p : is-prop A) where
  -- definitions using A and p
```

## 4. Cubical Agda Patterns

### Copattern Matching

Prefer copattern matching for record definitions. This gives better control
over definitional equalities and avoids unnecessary η-expansion.

When defining with many fields, sink "proof" fields towards the bottom.
Optionally include a blank line separating data from proofs:

```agda
-- Prefer:
ni .eta x .η _ = B.id
ni .inv x .η _ = B.id

ni .eta x .is-natural _ _ _ = B.id-comm-sym
ni .inv x .is-natural _ _ _ = B.id-comm-sym
ni .eta∘inv x = ext λ _ → B.idl _
ni .inv∘eta x = ext λ _ → B.idl _
```

### No-Eta-Equality

Use `no-eta-equality` as the **default** for records with multiple fields or
records containing proof-valued fields. This gives better control over which
telescopes the conversion checker examines.

**When to use `no-eta-equality`:**

1. **Multi-field records** — Any record with 2+ fields should use
   `no-eta-equality` unless there's a specific reason not to.

2. **Records with proof fields** — If any field's type is a proposition
   (like `paths : (y : A) → center ≡ y`), use `no-eta-equality`.

3. **Structure records** — Records defining algebraic structures, categories,
   equivalences, etc.

```agda
record Widget where
  no-eta-equality
  field
    carrier : Type
    operation : carrier → carrier
    ...

record is-contr {u} (A : Type u) : Type u where
  no-eta-equality  -- has proof field 'paths'
  field
    center : A
    paths : (y : A) → center ≡ y
```

**Exception: Single-field wrapper records** may use eta-equality when they
serve purely as newtype wrappers with no computational content:

```agda
-- Lift is a single-field wrapper — eta-equality is fine
record Lift {u} a (A : Type u) : Type (u ⊔ a) where
  constructor liftℓ
  field lower : A
```

**Rationale**: Eta-equality for multi-field records causes the conversion
checker to expand record values into their fields during unification, which
can be expensive. For single-field wrappers, this expansion is trivial.

Constructors of `no-eta-equality` records may be marked `INLINE` so Agda
converts applications to coclauses:

```agda
record Prebicategory o ℓ where
  no-eta-equality
  field
    Ob  : Type o
    Hom : Ob → Ob → Precategory ℓ ℓ'
  ...
{-# INLINE Prebicategory.constructor #-}
```

### H-Level Patterns

*Note: This section describes intended style. The automation machinery
(instance resolution, tactics like `prop!` and `hlevel!`) may not yet be
available in your codebase.*

For h-level (truncation level) handling:

- Define "leaf" instances in terms of a lower bound, not exact level
- Avoid local overlapping instances for assumptions like "this map is an
  embedding"
- Record types and datatypes should have `H-Level` instances
- Provide `!`-suffixed versions of definitions taking `is-hlevel` arguments
  that use instance resolution instead

### Wrapper Records for Definitional Injectivity

When defining a type family by recursion, wrap it in a single-field record
to make it definitionally injective:

```agda
record _≤_ (a b : ℚ) : Type where
  field lower : ...
```

Name the constructor `lift` and field `lower`.

### Pragmas

**INLINE**: Use for 1–3 line computational primitives (`coe*`, `refl`, `ap`,
`sym`) and `no-eta-equality` record constructors:

```agda
{-# INLINE Prebicategory.constructor #-}
```

**DISPLAY**: Use to hide internal `sys`/helper modules from goal output,
keeping interactive development focused on user-facing terms.

### Module Patterns

**Named modules for complex proofs**: Create `module foo` for definitions
exceeding ~10 lines with many internal helpers. This scopes the helpers and
makes the proof structure explicit.

**Parameter-scoped modules**: Use `module name {params}` to group related
derived operations sharing parameters:

```agda
module cat {p q : Ob} where
  -- operations on morphisms between p and q
```

**Module X import wrapping**: Wrap bulky stdlib imports in a private module,
re-exporting with renaming to control namespace pollution:

```agda
private module X = Data.List.Base
open X using (map; filter) renaming (foldr to fold)
```

**Definition-attached modules** (guideline): Attach `module foo` directly
after a definition to expose internal helpers when useful for downstream
proofs.

## 5. Algebraic Structures

Define algebraic structures in **property/structure/object** layers:

- **Property** (`is-widget`): Propositions about operations — must have
  `H-Level` instance
- **Structure** (`Widget-on`): Operations + properties, parametrised over
  carrier
- **Object** (`Widget`): Carrier bundled with structure

Homomorphisms follow the same pattern: `is-widget-hom` (preservation
conditions as propositions) separate from the bundled `Widget-hom`.

For universal objects, parametrise the property over the *entire* diagram
so it forms a proposition without strictness assumptions.

### Trait Record Conventions

Trait records (typeclass-like interfaces in `Core.Trait.*`) follow specific
conventions:

**Erasure**: Use `@0` annotations for law/property fields (proofs), but NOT
for structure fields (operations):

```agda
record Semigroup {u} (A : Type u) : Type u where
  no-eta-equality
  field
    _<>_ : A → A → A                    -- operation: NOT erased
    @0 assoc : ∀ x y z → ...            -- law: erased
```

**Rationale**: Operations must be available at runtime for computation. Laws
are only needed for type-checking proofs and can be erased.

**Constructor naming**: Do NOT use explicit `Mk*` constructor names. Use
Agda's implicit constructor:

```agda
-- Good: implicit constructor
record Eq {u} (A : Type u) : Type u where
  field _==_ : A → A → Bool

-- Avoid: explicit Mk* constructor
record Num {u} (A : Type u) : Typeω where
  constructor MkNum  -- Don't do this
  field ...
```

This aligns with how Eq, Ord, Semigroup, and other trait records are defined.

### Effect-Based Trait Instances

When defining instances for Effect-based traits (Functor, Applicative, Monad,
etc.), follow these conventions:

**No redundant Effect identifiers**: Do not create named Effect values like
`Maybe-Effect`. Use `eff Type` directly:

```agda
-- Good: use eff directly
private
  module M = Effect (eff Maybe)

instance
  Functor-Maybe : Functor (eff Maybe)

-- Avoid: redundant named Effect
Maybe-Effect : Effect
Maybe-Effect = eff Maybe  -- Don't do this
```

**Private helpers for instance implementations**: Helper functions used only
within instance definitions should be in a private block:

```agda
-- Good: helper in private block
private
  map-Maybe : (A → B) → Maybe A → Maybe B
  map-Maybe f nothing  = nothing
  map-Maybe f (just x) = just (f x)

instance
  Functor-Maybe : Functor (eff Maybe)
  Functor-Maybe .map = map-Maybe
  ...

-- Avoid: top-level helper only used internally
map-Maybe : (A → B) → Maybe A → Maybe B  -- Don't expose this
```

**No redundant section comments**: Do not use markdown headers like
`## Functor` or `## Monad` to label instance definitions. The instance
declaration itself is self-documenting:

```agda
-- Avoid:
## Functor

\`\`\`agda
instance
  Functor-Maybe : Functor (eff Maybe)
\`\`\`

-- Good: instance is self-documenting, no header needed
\`\`\`agda
instance
  Functor-Maybe : Functor (eff Maybe)
  ...
\`\`\`
```

If you must comment, use a brief inline note about the instance being defined,
not a section header.

## 6. Attribution

When adapting proofs or constructions from external sources, include attribution:

### Code Attribution

For code from libraries, cite the specific module:
```agda
-- Credit: 1lab, Equiv.Fibrewise
-- Credit: cubical, Cubical.Foundations.Equiv
-- Adapted from agda-unimath, foundation-core.contractible-types
```

### Literature Attribution

For papers/books, cite with section/theorem when available:
```agda
-- Following Rijke, Theorem 11.2.4
-- From Capriotti–Kraus (arXiv:1707.03693), Section 3.2
-- Based on Petrakis (arXiv:2205.06651), Definition 2.1
```

### Module Header Attribution

For significant derivations, acknowledge in the module's opening prose with
specific modules/sections cited:

```markdown
The H-Level automation machinery is largely derived from 1lab's
Data.Nat.Properties and Equiv.Fibrewise modules, with additional
influence from Chen's semicategories-with-identities formalization.
```

### When Attribution Is Required

- Adapting a proof strategy from a paper or book
- Translating code from another library (1lab, cubical, agda-unimath)
- Implementing a construction following a specific reference
- Using a non-obvious technique learned from external sources

Attribution is not needed for standard constructions that are "obvious" or
widely known (e.g., basic path operations, standard recursion patterns).

## 7. Documentation Style

Use `.lagda.md` for mathematically interesting content; reserve `.agda` for
metaprogramming, prelude/re-export, and notation modules.

Prefer mathematical clarity over verbose comments — code should be
self-documenting through good naming and structure.

### Comments and Prose

**Comments are a last resort.** Well-structured code with good naming should be
self-explanatory. Introduce comments only when the code alone does not suffice
for understanding. When comments are necessary, follow a concise and technical
expository style.

**Multi-line comments belong in markdown.** If a comment exceeds 2 lines, write
it as prose outside the code block, with the code following inside:

```markdown
The key insight is that fibers of `tot f` are equivalent to fibers of `f a`
at each point. This follows from the fact that paths in Σ-types decompose
into paths in the base and dependent paths in the fiber.

\`\`\`agda
fib-tot : fiber (tot f) (a , c) ≃ fiber (f a) c
\`\`\`
```

**Avoid redundant comments.** Do not write comments that merely restate what
the type signature already expresses:

```agda
-- Bad: comment restates the type
-- bi-inv → equiv via qinv
bi-inv→equiv : is-bi-inv f → is-equiv f

-- Good: the type is self-documenting
bi-inv→equiv : is-bi-inv f → is-equiv f
```

```agda
-- Also bad: plain-English translation of the type
-- S k < k is absurd
sn<n-absurd : (k : Nat) → ¬ (S k < k)

-- Good: the negation is self-explanatory
sn<n-absurd : (k : Nat) → ¬ (S k < k)
```

**Use equational reasoning for non-trivial proofs.** Do not write step-by-step
comments for proofs — either the proof is short enough to be self-evident, or
it warrants equational reasoning notation:

```agda
-- Bad: step-by-step comments for a trivial proof
-- Step 1: ap h (ε (f x)) : h (f (g (f x))) ≡ h (f x)
-- Step 2: η x : h (f x) ≡ x
sec' x = ap h (ε (f x)) ∙ η x

-- Good: let the proof speak for itself
sec' x = ap h (ε (f x)) ∙ η x

-- Good: use equational reasoning for complex proofs
sec' x =
  h (f (g (f x))) ≡⟨ ap h (ε (f x)) ⟩
  h (f x)         ≡⟨ η x ⟩
  x               ∎
```

### Blank Lines

- Single blank line between definitions within a logical group
- **Double blank lines** between semantic groups (e.g., separating basic
  operations from derived lemmas)
- No blank line between a type signature and its definition

### Markdown Conventions

- ATX-style headers (`## Section`), not setext-style
- Use `## SectionName` headers to organize major definition groups in
  `.lagda.md` files
- Asterisks for emphasis (`*italic*`, `**bold**`)
- Sentence case for headers, except proper names

## 8. Erasure and Cubical Flags

### Module Flags

The library uses `--erased-cubical` as the default. This provides cubical
primitives with erased computational content, which is sufficient for most
proofs and improves performance.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}
```

### Global Library Flags

The `kitcat.agda-lib` file sets these flags library-wide:

- `--no-sized-types` — disabled globally (can be redundantly included per-module)
- `--erasure` — enables `@0` annotations
- `-Werror` — warnings are errors
- Quality flags: `--exact-split`, `--auto-inline`, etc.

### Disabling Unused Features

**Policy**: If a module does not use a feature, explicitly disable it in the
module header.

- **`--no-guardedness`**: Include when the module doesn't use corecursion or
  guardedness. Most modules don't need guardedness and should include this flag.
- **`--no-sized-types`**: Already global, but can be included for explicitness.

This makes module dependencies explicit and catches accidental usage of features.

### When to Use `--cubical-compatible`

Use `--cubical-compatible` (instead of `--erased-cubical`) for modules that:

- Do **not** import any cubical primitives (`I`, `PathP`, `hcomp`, etc.)
- Define only universe-polymorphic types and combinators
- Serve as a "pure" foundation layer (e.g., `Core.Prim`)

This allows the module to be imported by both cubical and non-cubical code.
Modules using `--cubical-compatible` cannot use path types or cubical
operations — they are restricted to standard Agda features.

```agda
-- Example: Core.Prim uses --cubical-compatible because it only defines
-- Level, Type, Lift, id, const, _∘_, etc. — no cubical primitives.
{-# OPTIONS --safe --cubical-compatible #-}
```

### When to Use `--cubical`

Use full `--cubical` only when the module requires:

- **Glue types** — needed for univalence (`ua`, `Glue`)
- **Computational univalence** — when `transport (ua e) a` must compute to
  `e .fst a` at runtime (rare)

Modules using `--cubical` should include a header note explaining why:

```markdown
This module uses `--cubical` (not `--erased-cubical`) because the Glue type
primitives require full cubical. Modules importing this can still use
`--erased-cubical`.
```

### `@0` Annotations

Use `@0` (erased) annotations when:

- A parameter is only used in types/propositions, not computationally
- Enabling callers to pass erased arguments
- Improving runtime performance by marking proof-only data

```agda
-- Good: A is only used in the type, not the computation
swap : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A × B → B × A
swap (a , b) = b , a
```

**When NOT to erase:**

```agda
-- Keep computational content (n is used at runtime)
compute : (n : Nat) → Vec A n

-- Keep what's needed for extraction/compilation
inv : B → A  -- Don't erase function results

-- Keep indices needed for pattern matching
ind : (n : Nat) → P n  -- n might be matched on
```
