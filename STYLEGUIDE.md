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

**Multi-line signatures with colon on next line**: When a type signature is
too long for one line and the colon starts on the next line, arrows in
continuing lines **must** be aligned with the colon:

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
```

**Multi-line signatures with colon on same line**: When the colon stays on
the same line, arrows align with the content after the colon:

```agda
-- Fine:
ap : ∀ {u v} {@0 A : Type u} {@0 B : A → Type v}
   → (f : ∀ x → B x) {x y : A} (p : x ≡ y)
   → PathP (λ i → B (p i)) (f x) (f y)
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

-- Never:
foo = {! code !}
  where
    bar = ...
```

If the RHS spans multiple lines, `where` goes on its own continuation line
at the same indentation as the RHS, with declarations indented one step
from `where`:

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

### Blank Lines

- Single blank line between definitions within a logical group
- **Double blank lines** between semantic groups (e.g., separating basic
  operations from derived lemmas)
- No blank line between a type signature and its definition

## 2. Naming Conventions

### General Style

Use `kebab-case` as the default naming convention.

### Generic Algebraic Identifiers

Use **noun-adjective order**: `{noun}{adjective}` not `{adjective}{noun}`.

| Generic | Meaning                    | Left/Right Laws   |
|---------|----------------------------|-------------------|
| `unit`  | unit/identity              | `unitl`, `unitr`   |
| `inv`   | inversion/symmetry         | `invl`, `invr`    |
| `cat`   | concatenation/transitivity | `catl`, `catr`    |

Law naming pattern: `{trait-prefix}{generic}{side}`

Examples:
- Path groupoid: `unitl : p ∙ refl ≡ p`, `invl : sym p ∙ p ≡ refl`
- Monoid: `munitl : mempty <> x ≡ x`, `munitr : x <> mempty ≡ x`
- Group: `ginvl : ginv x <> x ≡ mempty`, `ginvr : x <> ginv x ≡ mempty`

This convention applies across `Core.Kan` (path laws), `Core.Homotopy`
(homotopy laws), and `Core.Trait.*` (algebraic structure laws).

Within qualified operation namespaces, use the standard law vocabulary
from §4 Tier 2 directly: `Ty.add.comm`, `Ty.add.unitl`. The
trait-prefixed forms (`munitl`, `ginvl`) apply to unqualified contexts.

### Departures from Rijke

| Rijke       | Kitcat              | Rationale                              |
|-------------|---------------------|----------------------------------------|
| `inv`       | `sym`               | Avoids conflict with `htpy.inv`        |
| `concat`    | `_∙_`               | Standard cubical operator              |
| `tr`        | `transport`/`subst` | Explicit over cryptic                  |
| `iscontr`   | `is-contr`          | Kebab-case per style guide             |
| `isprop`    | `is-prop`           | Same                                   |
| `isset`     | `is-set`            | Same                                   |
| `left-unit` | `unitl`             | Noun-adjective order                   |
| `right-unit`| `unitr`             | Same                                   |
| `left-inv`  | `invl`              | Noun-adjective order                   |
| `right-inv` | `invr`              | Same                                   |

Preserved from Rijke: `refl`, `ap`, `apd`, `_~_`, `≃`, `is-equiv`

### Pattern Synonyms

`Z` and `S` are pattern synonyms for `zero` and `suc` (defined in
`Core.Type.Nat`).

### CamelCase Exceptions

Two categories of identifiers use `camelCase` instead of `kebab-case`:

**1. Trait record fields** — Following Idris2 Prelude conventions:

```agda
record Num {u} (A : Type u) : Typeω where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    fromInteger : Int → A
```

This distinguishes trait automation from mathematical definitions.
Instance names still use `kebab-case` with the trait name: `Trunc-Π`,
`Num-Nat`.

**2. Primitive/builtin identifiers** — Following Agda conventions:

```agda
primHComp, primTransp, primINeg, primIMax, primIMin
putStrLn, getLine, readFile
```

Primitives use `camelCase` (often with a `prim` prefix) to match Agda's
builtin naming and to visually distinguish low-level primitives from
library code.

### Symbol Separators

Replace words with symbols where appropriate:

| Word/Phrase      | Symbol |
|------------------|--------|
| "to", "implies"  | `→`   |
| "equivalent to"  | `≃`   |
| "equal to"       | `≡`   |

Examples: `is-equiv→is-embedding`, `Ωⁿ≃Sⁿ-map`, `PathP≡Path`

**Whiskering operators**: Use `_▹_` for left whiskering (path on the
left) and `_◃_` for right whiskering (path on the right).

### Conversion Primitives

Fundamental type-conversion functions use compressed naming without
hyphens: `eqvtofun`, `idtofun`, `pathtofun`, `eqvtoinv`. This
distinguishes core coercion primitives from derived operations.

### Predicates and Propositions

Names of propositions should start with `is-`: `is-equiv`, `is-group-hom`

Names of more general types should start uppercase: `Group-on`, `Glue`

In theorems, the predicate appears after the thing it applies to:
`Nat-is-set`, not `is-set-Nat`. When an aggregator module provides a
namespace (e.g. `module Nat`), prefer `Nat.set` over `Nat-is-set`.

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

This aligns with the Predicates and Propositions convention — records
bundling properties use lowercase prefixes, while structures use
capitalized names.

### Duality Naming

For dual concepts:

- The "concrete dual" should be a single word: `Coproduct`
- The categorical dual uses `co-` as a prefix: `co-product`

Hence: `is-coproduct→is-co-product`

### Displayed/Dependent Versions

The displayed version of a `Thing` may be called `ThingP`, following
the pattern of `PathP` and `SquareP`.

### Homotopy Operators

Two homotopy types are used:

- `_~_` — pointwise homotopy: `f ~ g = ∀ x → f x ≡ g x`
- `_~ᵢ_` — interval-indexed homotopy: `f ~ᵢ g = ∀ i → f i ≡ g i`

### Variables and Parameters

- Generalizable variables are encouraged for cleaning up long telescopes
- Do not export generalizable variables
- Explicitly annotate binders when instance search involves indeterminate
  types

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

## 3. Documentation Style

Use `.lagda.md` for mathematically interesting content; reserve `.agda`
for metaprogramming, prelude/re-export, and notation modules.

Prefer mathematical clarity over verbose comments — code should be
self-documenting through good naming and structure.

### Comments and Prose

**Comments are a last resort.** Well-structured code with good naming
should be self-explanatory. Introduce comments only when the code alone
does not suffice for understanding. When comments are necessary, follow a
concise and technical expository style.

**Multi-line comments belong in markdown.** If a comment exceeds 2 lines,
write it as prose outside the code block, with the code following inside:

```markdown
The key insight is that fibers of `tot f` are equivalent to fibers of
`f a` at each point. This follows from the fact that paths in Σ-types
decompose into paths in the base and dependent paths in the fiber.

\`\`\`agda
fib-tot : fiber (tot f) (a , c) ≃ fiber (f a) c
\`\`\`
```

**Avoid redundant comments.** Do not write comments that merely restate
what the type signature already expresses:

```agda
-- Bad: comment restates the type
-- bi-inv → equiv via qinv
bi-inv→equiv : is-bi-inv f → is-equiv f

-- Good: the type is self-documenting
bi-inv→equiv : is-bi-inv f → is-equiv f
```

**Use equational reasoning for non-trivial proofs.** Do not write
step-by-step comments for proofs — either the proof is short enough to
be self-evident, or it warrants equational reasoning notation:

```agda
-- Bad: step-by-step comments
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

### Markdown Conventions

- ATX-style headers (`## Section`), not setext-style
- Use `## SectionName` headers to organize major definition groups in
  `.lagda.md` files
- Asterisks for emphasis (`*italic*`, `**bold**`)
- Sentence case for headers, except proper names

## 4. Module Organization

### Namespace Structure

**Default: single-file with qualified-access module.** When a type has
operations and properties, define everything in one file with a
`module Ty where` block for qualified access. This is the starting
point for every namespace — split into multiple files only when the
single file grows unwieldy (roughly >200 lines of Agda) or when
circular dependencies force separation.

```agda
module Core.Function.Pullback where

-- Top-level: type definition (unqualified access)
Pullback : (f : A → C) (g : B → C) → Type _
Pullback f g = ...

-- Qualified access: Pullback.inl, Pullback.swap, etc.
module Pullback where
  inl : Pullback f g → A
  swap : Pullback f g ≃ Pullback g f
```

Use a qualified-access module wherever it makes ergonomic sense —
even small namespaces benefit from `Ty.op` access patterns. The
multi-file hierarchy below is for namespaces that outgrow a single
file, not the default starting point.

**Multi-file hierarchy.** For namespaces that outgrow a single file
(~200 lines), use this hierarchical structure:

**Directory layout for type `Ty`:**

```
Ty/
├── Type.lagda.md      (optional: raw type definition only)
├── Base.lagda.md      (basic operations, no proofs)
├── <Op>.lagda.md      (proofs about operation <Op>)
├── <Op>/              (optional: subhierarchy)
│   ├── Base.lagda.md
│   └── Properties.lagda.md
├── Impl/
│   └── <Trait>.lagda.md   (trait implementations)
└── Properties.lagda.md    (aggregates all properties)
Ty.lagda.md            (aggregator in parent namespace)
```

**Module responsibilities:**

| Module | Purpose | Allowed Imports |
|--------|---------|-----------------|
| `Ty/Type` (optional) | Raw type definition | `Core.Type`, `Core.Base` only |
| `Ty/Base` | Basic operations (no proofs) | `Ty.Type` + external, NOT siblings |
| `Ty/<Op>` | Proofs about `<Op>` | `Ty.Type`, `Ty.Base`, external |
| `Ty/Impl/<Trait>` | Trait implementation | As needed; only instance is public |
| `Ty/Properties` | Aggregates properties | All `Ty/*` modules |

**Impl modules**: Only the instance itself should be exported; all helper
definitions should be private.

**Properties aggregation**: For small namespaces, `Properties.lagda.md`
contains properties directly. For larger namespaces, it re-exports from
`<Op>/Properties.lagda.md` modules:

```agda
module add where
  open import Ty.Add.Properties public

module mul where
  open import Ty.Mul.Properties public
```

**Aggregator module (`Ty.lagda.md`)**: Lives in the parent namespace and
controls the public API:

```agda
-- Top-level: type + constructors
open import Ty.Type public

-- Namespaced: operations, properties, and trait implementations
module Ty where
  open import Ty.Base public
  open import Ty.Properties public

  module impl where
    open import Ty.Impl.Eq public
    open import Ty.Impl.Ord public
```

This gives users `Ty` and its constructors at top level, while operations
and properties are accessed as `Ty.op` and `Ty.op.property`.

**Reference implementation**: The `Nat` namespace follows this format.

### Reserved identifiers for qualified namespaces

When building a `module Ty where` namespace, use the following standard
vocabulary. This ensures predictable naming across the library — users
can guess `Ty.set`, `Ty.add.comm`, etc. without checking documentation.

#### Tier 1: `Ty.*` — Base namespace

Identifiers available directly as `Ty.name`:

**Eliminators and recursors:**

| Name   | Purpose                        |
|--------|--------------------------------|
| `ind`  | Induction principle            |
| `rec`  | Recursion principle            |
| `elim` | Eliminator (synonym for `ind`) |
| `iter` | Iteration principle            |
| `fold` | Fold (also `foldl`, `foldr`)   |
| `map`  | Functorial mapping             |

`map` and `fold` may alternatively live in trait instances only (`Map`,
`Foldable`). Both conventions are allowed — some types define `Ty.map`
as the concrete implementation (with the trait delegating to it), others
only provide the trait instance.

**Algebraic structure:**

| Name   | Purpose                           |
|--------|-----------------------------------|
| `inv`  | Inverse operation (computational) |
| `zero` | Zero element                      |
| `one`  | One element                       |
| `unit` | Canonical unit element            |
| `suc`  | Successor function                |
| `pred` | Predecessor function              |
| `cmp`  | Comparison/decision procedure     |

For types with multiple operations (e.g., a ring), omit `Ty.unit` and
use `Ty.<op>.unit` per operation instead. Reserve `Ty.unit` for types
with a single canonical identity element.

**H-level proofs:**

| Name    | Type             | When                      |
|---------|------------------|---------------------------|
| `prop`  | `is-prop Ty`     | Type is a proposition     |
| `set`   | `is-set Ty`      | Type is a set             |
| `trunc` | `is-hlevel n Ty` | H-level > 2               |

Already in use: `Nat.set`, `Bool.set`, `Fin.set`, `Bin.set`.

**Type-level relations:**

| Name | Purpose                                      |
|------|----------------------------------------------|
| `Eq` | Equality relation `Ty → Ty → Type`           |
| `rx` | Reflexivity (binary relation types only)      |

`Eq` is capitalized because it is a Type former (per §2 Record Types
convention). `rx` follows the reflexive graph framework convention.

**Operators** (for `open Ty` notation access):

| Operator | Literal name | Purpose            |
|----------|-------------|--------------------|
| `_+_`    | `add`       | Addition           |
| `_-_`    | `sub`       | Subtraction        |
| `_*_`    | `mul`       | Multiplication     |
| `_⨾_`    | `cat`       | Composition        |
| `_<_`    | `lt`        | Strict order       |
| `_≤_`    | `le`        | Non-strict order   |
| `_>_`    | `gt`        | Reverse strict order |

The literal names (`add`, `sub`, `mul`, `cat`) are the sub-namespace
names for the operation's laws (Tier 2).

#### Tier 2: `Ty.<op>.*` — Operation sub-namespaces

Laws and properties for a specific operation, accessed as
`Ty.add.comm`, `Ty.mul.assoc`, etc. The `<op>` name is the literal
name from the operator table above, or any descriptive name for
non-operator operations (e.g., `and`, `or`, `xor`, `not`, `concat`).

**Core laws:**

| Name      | Purpose                  |
|-----------|--------------------------|
| `comm`    | Commutativity            |
| `assoc`   | Associativity            |
| `unitl`   | Left unit law            |
| `unitr`   | Right unit law           |
| `invl`    | Left inverse law         |
| `invr`    | Right inverse law        |
| `injl`    | Left injectivity         |
| `injr`    | Right injectivity        |

**Extended laws:**

| Name      | Purpose                           |
|-----------|-----------------------------------|
| `zerol`   | Left zero/annihilation (`0 * x ≡ 0`) |
| `zeror`   | Right zero/annihilation (`x * 0 ≡ 0`)|
| `idem`    | Idempotence                       |
| `invol`   | Involution (`f (f x) ≡ x`)       |
| `distl`   | Left distributivity               |
| `distr`   | Right distributivity              |

**Unit element:** `Ty.<op>.unit` is the unit element of this specific
operation, when it differs from `Ty.unit` in the base namespace.

**Cross-operation laws** like distributivity concern the interaction
of two operations, not a single one. These belong at the parent
namespace level (`Ty.distl`, `Ty.distr`), not inside either operation
sub-namespace.

**Dual law prefix:** For `co` versions of laws within operation
namespaces, prefix `co` without a separator: `cocomm`, `coassoc`, etc.
This is distinct from the §2 Duality Naming convention for type names,
which uses `co-` with a hyphen.

#### Tier 3: Ordering sub-namespaces

Ordering relations follow the same operator/module pattern as
arithmetic: the operators (`_<_`, `_≤_`, `_>_`) live at Tier 1, and
their literal names (`lt`, `le`, `gt`) are Tier 2 sub-namespaces for
laws. For example: `Ty.lt.cat` (transitivity of `<`),
`Ty.le.rx` (reflexivity of `≤`).

Cross-relation lemmas belong at the parent namespace level with
plaintext names: `Ty.lt-le-cat` rather than `Ty.<≤-cat`.

#### Tier 4: `Ty.impl` — Trait instances

Trait instances grouped under a `module impl where` sub-namespace in
the aggregator (see aggregator example above). Instance resolution
works correctly through nested `open public` re-exports — consumers
do not need to explicitly `open Ty.impl`.

**Note on `--no-qualified-instances`:** Under Agda's default behavior
(which Kitcat uses), all instances are candidates for resolution even
behind qualified names — so `module impl where` is purely
organizational. If `--no-qualified-instances` were ever adopted,
`impl` would become a visibility gate requiring consumers to
`open Ty.impl` to opt into instances.

### Import Ordering

Imports should be grouped by the first component of the module path,
with groups sorted alphabetically.

Within groups, sort by module path length (longest path first).

Order statement types: `open import`, then `import`, then `open`.

### Private Variable Blocks

Declare private variables at the top of the module, immediately after
imports:

```agda
private variable
  u v : Level
  m n k : Nat
```

### Private Declarations

Use `private` blocks for internal helpers.

### Module Aliases

Use private module aliases for namespace management:

```agda
private
  module C = Cat.Reasoning C
```

Instantiated module aliases must not be exported from parametrised
anonymous modules.

### Utility Modules

Group related helper functions under a named module when they form a
coherent API:

```agda
module ∂ where
  contract : ...
  extend   : ...
  cover    : ...
  sym      : ...
```

This scopes the helpers and provides qualified access (`∂.contract`,
`∂.extend`).

### Property Modules Layered on Definitions

In Agda, module and definition identifiers occupy separate namespaces.
A `module not` can coexist with a function `not` in the same scope.
Use this to attach property submodules directly to the operation they
describe:

```agda
module not where
  invol : ∀ b → not (not b) ≡ b

module and where
  comm  : ∀ a b → and a b ≡ and b a
  assoc : ∀ a b c → and a (and b c) ≡ and (and a b) c
```

After re-export through an aggregator, this gives `Bool.not` for the
function and `Bool.not.invol` for the lemma. Prefer this over suffixed
names like `not-laws` or `not-properties`.

### Anonymous Modules for Parameter Sharing

Use `module _` to share parameters across related definitions:

```agda
module _ {A : Type} (p : is-prop A) where
  -- definitions using A and p
```

### The All Module

`src/All.lagda.md` is the whole-library typecheck target. Every new
non-Stash module must be reflected in `All`.

- Import **aggregator modules only** — do not list sub-modules already
  covered by an aggregator (e.g. `import Core.Data.Nat`, not
  `Core.Data.Nat.Base` + `Core.Data.Nat.Properties`).
- Use plain `import` (not `open import`); `All` exists for
  typechecking, not re-export.
- Comment out WIP modules that don't yet typecheck, with a reason.

## 5. Cubical Agda Patterns

### Module Flags

The library uses `--erased-cubical` as the default:

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}
```

The `kitcat.agda-lib` file sets these flags library-wide:

- `--no-sized-types` — disabled globally (do not repeat per-module)
- `--erasure` — enables `@0` annotations
- `-Werror` — warnings are errors
- Quality flags: `--exact-split`, `--auto-inline`, etc.

**`--no-guardedness`**: Include when the module doesn't use corecursion.
Most modules should include this flag.

### `--cubical-compatible`

Use `--cubical-compatible` (instead of `--erased-cubical`) for modules
that:

- Do **not** import any cubical primitives (`I`, `PathP`, `hcomp`, etc.)
- Define only universe-polymorphic types and combinators
- Serve as a "pure" foundation layer (e.g., `Core.Prim`)

```agda
{-# OPTIONS --safe --cubical-compatible #-}
```

### `--cubical`

Use full `--cubical` only when the module requires:

- **Glue types** — needed for univalence (`ua`, `Glue`)
- **Computational univalence** — when `transport (ua e) a` must compute

Modules using `--cubical` should include a header note explaining why.

### Copattern Matching

Prefer copattern matching for record definitions. This gives better
control over definitional equalities and avoids unnecessary η-expansion.

When defining with many fields, sink "proof" fields towards the bottom.
Optionally include a blank line separating data from proofs:

```agda
ni .eta x .η _ = B.id
ni .inv x .η _ = B.id

ni .eta x .is-natural _ _ _ = B.id-comm-sym
ni .inv x .is-natural _ _ _ = B.id-comm-sym
ni .eta∘inv x = ext λ _ → B.idl _
ni .inv∘eta x = ext λ _ → B.idl _
```

### `no-eta-equality`

Use `no-eta-equality` as the **default** for records with multiple fields
or records containing proof-valued fields. This prevents the conversion
checker from expanding record values into their fields during
unification.

**When to use:**

1. **Multi-field records** — Any record with 2+ fields
2. **Records with proof fields** — If any field is proposition-valued
3. **Structure records** — Algebraic structures, categories, equivalences

```agda
record is-contr {u} (A : Type u) : Type u where
  no-eta-equality
  field
    center : A
    paths : (y : A) → center ≡ y
```

**Exception: Single-field wrapper records** may use eta-equality when
they serve purely as newtype wrappers:

```agda
record Lift {u} a (A : Type u) : Type (u ⊔ a) where
  constructor liftℓ
  field lower : A
```

### `INLINE` Pragmas

Use `INLINE` for:

1. **`no-eta-equality` record constructors** — so Agda converts
   constructor applications to copattern matches:

   ```agda
   {-# INLINE Cat.constructor #-}
   ```

2. **1–3 line computational primitives** — `coe*`, `refl`, `ap`, `sym`

3. **Small operator definitions** — `δ□`, `σ□`, `comp□`

### `DISPLAY` Pragmas

Use `DISPLAY` to hide internal helper modules from goal output, keeping
interactive development focused on user-facing terms:

```agda
{-# DISPLAY hcom.sys-base φ u a = hcom φ u a #-}
```

### `@0` Annotations

Use `@0` (erased) annotations when a parameter is only used in
types/propositions, not computationally:

```agda
swap : ∀ {u v} {@0 A : Type u} {@0 B : Type v} → A × B → B × A
swap (a , b) = b , a
```

For trait records, erase **law fields** (proofs) but not **operation
fields** (computational content):

```agda
record Semigroup {u} (A : Type u) : Type u where
  no-eta-equality
  field
    _<>_ : A → A → A              -- operation: NOT erased
    @0 assoc : ∀ x y z → ...      -- law: erased
```

**When NOT to erase:**

- Parameters used at runtime (`(n : Nat) → Vec A n`)
- Function results (`inv : B → A`)
- Indices needed for pattern matching

### Wrapper Records for Definitional Injectivity

When defining a type family by recursion, wrap it in a single-field
record to make it definitionally injective:

```agda
record _≤_ (a b : ℚ) : Type where
  field lower : ...
```

Name the constructor `lift` and field `lower`.

### Decidability over Bool

Prefer decidable type-valued predicates over `Bool`-valued encodings.
In dependent type theory, `Bool`-valued predicates are an antipattern
outside of interfaces to lower-level programs — they discard the
proof-relevant structure that types carry.

When a predicate needs to be a set (e.g. for use in an `SSet` record
that requires `Cell-is-set`), the correct approach is:

1. Define the predicate as a type family (`R : A → A → Type`)
2. Prove it is decidable (`∀ x y → Dec (R x y)`)
3. Derive sethood via `hedberg`

A genuine relation should additionally be propositional (`is-prop`),
but this is a separate design choice — decidability alone gives
sethood, not propositionality.

```agda
-- Good: decidable type-valued relation
R     : Fin (S n) → Fin (S n) → Type
R-dec : ∀ i j → Dec (R i j)
-- Then: hedberg gives is-set for the containing type

-- Avoid: Bool-valued encoding
rel : Fin (S n) → Fin (S n) → Bool
-- Discards structure, gains nothing over Dec
```

This pattern is established throughout the library: `DecEq-Nat` and
`DecEq-Bool` both feed into `hedberg` to produce `Nat.set` and
`Bool.set`.

### H-Level Patterns

The `Trunc` trait in `Core.Trait.Trunc` provides h-level automation via
instance resolution, derived from 1lab's H-Level machinery.

- Define "leaf" instances in terms of a lower bound, not exact level
  (use `basic-trunc`, `prop-trunc`, `set-trunc`, `contr-trunc`)
- Avoid local overlapping instances
- Record types and datatypes should have `Trunc` instances
- Use `!`-suffixed entry points: `trunc!` for contractibility,
  `prop!` for propositional path filling

### Module Patterns

**Named modules for complex proofs**: Create `module foo` for
definitions exceeding ~10 lines with many internal helpers. This scopes
the helpers and makes the proof structure explicit.

**Parameter-scoped modules**: Use `module name {params}` to group
related derived operations sharing parameters:

```agda
module cat {p q : Ob} where
  -- operations on morphisms between p and q
```

**Definition-attached modules**: Attach `module foo` directly after a
definition to expose internal helpers when useful for downstream proofs.

### Mutual Data Definitions

When defining data types with associated projection functions that need
definitional reduction, define them mutually with direct constructor
matching:

```agda
data Spine {X : Type u} (H : X -> X -> Type v)
  : Nat -> Type (u ⊔ v)

vertex
  : ∀ {n} -> Fin (S n) -> Spine H n -> X

data Spine H where
  [_] : X -> Spine H Z
  _⨾_ : (s : Spine H n) -> H x (vertex fzero s) -> Spine H (S n)

vertex _ [ x ] = x
vertex fzero (_⨾_ {x = x} s h) = x
vertex (fin (S k) ...) (_⨾_ s h) = vertex (fin k ...) s
```

Match on the `fin` constructor directly (not `fin-view`) so the
definition reduces definitionally and dependent types in downstream
definitions work out.

## 6. Record and Data Patterns

### Records vs Sigma Types

Prefer **records** over nested Σ-types when a type has more than two
projections. Records provide named fields, better error messages, and
`no-eta-equality` control.

**Use Σ-types** for:
- Simple pairs with two projections (e.g., `fiber f y = Σ x , f x ≡ y`)
- Inline existential witnesses in proof terms
- Cases where Σ-path reasoning is the primary proof technique

**Use records** for:
- Structures with 3+ fields (e.g., `is-equiv`, `is-contr`, `Cat`)
- Types that benefit from `no-eta-equality` (performance-sensitive types)
- Types with derived operations (records support inline definitions)
- Core bottleneck types where definitional behavior matters

**Exception:** Core types that appear in many unification problems (e.g.,
`is-contr`, `is-equiv`) should use records even for 2 fields, because
`no-eta-equality` prevents expensive eta-expansion during typechecking.

Evaluate on a case-by-case basis — the guiding principle is that records
are the default for anything beyond a simple pair, with Σ reserved for
lightweight existentials.

### Algebraic Structures

Define algebraic structures in **property/structure/object** layers:

- **Property** (`is-widget`): Propositions about operations — must have
  `H-Level` instance
- **Structure** (`Widget-on`): Operations + properties, parametrised
  over carrier
- **Object** (`Widget`): Carrier bundled with structure

Homomorphisms follow the same pattern: `is-widget-hom` (preservation
conditions as propositions) separate from the bundled `Widget-hom`.

For universal objects, parametrise the property over the *entire* diagram
so it forms a proposition without strictness assumptions.

### Trait Record Conventions

Trait records (typeclass-like interfaces in `Core.Trait.*`) follow:

- **`no-eta-equality`** on all trait records (§5)
- **`@0` on law fields**, not operation fields (§5, @0 Annotations)
- **No explicit `Mk*` constructors** — use Agda's implicit constructor

```agda
-- Good: implicit constructor
record Eq {u} (A : Type u) : Type u where
  field _==_ : A → A → Bool

-- Avoid: explicit Mk* constructor
record Num {u} (A : Type u) : Typeω where
  constructor MkNum  -- Don't do this
  field ...
```

### Effect-Based Trait Instances

When defining instances for Effect-based traits:

- Use `eff Type` directly; do not create named Effect values
- Place helper functions in `private` blocks
- Instance declarations are self-documenting; avoid redundant section
  headers

## 7. Attribution

When adapting proofs or constructions from external sources, include
attribution.

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

For significant derivations, acknowledge in the module's opening prose
with specific modules/sections cited.

### When Attribution Is Required

- Adapting a proof strategy from a paper or book
- Translating code from another library (1lab, cubical, agda-unimath)
- Implementing a construction following a specific reference
- Using a non-obvious technique learned from external sources

Attribution is not needed for standard constructions that are "obvious"
or widely known (e.g., basic path operations, standard recursion
patterns).
