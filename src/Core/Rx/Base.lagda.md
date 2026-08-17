---
author: Lane Biocini
date: 2026-08-04
last-modified: 2026-08-09
---

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Rx.Base where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Kan using (_∙_)
open import Core.Equiv using (_≃_; aut)
open import Core.Transport.Base using (transport; transport-filler)
open import Core.Transport.Properties using (prop-inhabited→is-contr)

open import Core.Rx.Type
```

A helper describing a dependent reflexive graph family on an arbitrary type.

```agda
dep-rx : ∀ {ℓ} (w z : Level) (A : Type ℓ) → Type (ℓ ⊔ w ₊ ⊔ z ₊)
dep-rx w z A = A → reflexive-graph w z
```

The *product* and *coproduct* of a type-indexed family of reflexive
graphs take dependent functions and dependent pairs on vertices; a
coproduct edge carries an identification of indices, along which the
source vertex transports.

```agda
module _ {ℓ w z} (A : Type ℓ) (B : dep-rx w z A) where
  private module B x = reflexive-graph (B x)

  product : reflexive-graph (ℓ ⊔ w) (ℓ ⊔ z)
  product .reflexive-graph.vtx      = (x : A) → B.vtx x
  product .reflexive-graph.edge f g = (x : A) → B.edge x (f x) (g x)
  product .reflexive-graph.rx f x   = B.rx x (f x)

  coproduct : reflexive-graph (ℓ ⊔ w) (ℓ ⊔ z)
  coproduct .reflexive-graph.vtx = Σ x ∶ A , B.vtx x
  coproduct .reflexive-graph.edge (a₀ , b₀) (a₁ , b₁) =
    Σ p ∶ a₀ ≡ a₁ , B.edge a₁ (transport (λ i → B.vtx (p i)) b₀) b₁
  coproduct .reflexive-graph.rx (a , b) =
    refl , transport (λ j → B.edge a (transport-filler (λ i → B.vtx a) b j) b) (B.rx a b)

module rx {v e} (G : reflexive-graph v e) where
  open reflexive-graph G
```

*vfam* is a dependent type family depending on the vertices of a
reflexive-graph V, and *efam* depends on its edges; the lens
constructions are indexed by one or the other. We make the indices
explicit in the latter case because it is often necessary for good
computational behavior.

```agda

  vfam : (w z : Level) → Type (v ⊔ w ₊ ⊔ z ₊)
  vfam w z = dep-rx w z vtx

  efam : (w z : Level) → Type (v ⊔ e ⊔ w ₊ ⊔ z ₊)
  efam w z = (x y : vtx) → edge x y → reflexive-graph w z
```

A displayed reflexive graph over `G` is the other structure the
interface carries.  The *diagonal* of an edge family restricts it to
the reflexive edges, recovering a vertex family.

```agda
  disp : (w z : Level) → Type (v ⊔ e ⊔ w ₊ ⊔ z ₊)
  disp w z = reflexive-graphᴰ w z G

  diag : ∀ {w z} → efam w z → vfam w z
  diag B x = B x x (rx x)
```

The *tensor* and *cotensor* of a graph by a type are the coproduct and
product of the constant family.

```agda
  tensor : ∀ {ℓ} (A : Type ℓ) → reflexive-graph (ℓ ⊔ v) (ℓ ⊔ e)
  tensor A = coproduct A (λ _ → G)

  cotensor : ∀ {ℓ} (A : Type ℓ) → reflexive-graph (ℓ ⊔ v) (ℓ ⊔ e)
  cotensor A = product A (λ _ → G)
```

The outgoing edges from a vertex form its *fan*; the incoming edges form its
*cofan*. Reflexivity gives each a distinguished center.

```agda
  fan : vtx → Type (v ⊔ e)
  fan x = Σ y ∶ vtx , edge x y

  cofan : vtx → Type (v ⊔ e)
  cofan y = Σ x ∶ vtx , edge x y

  fan-center : ∀ x → fan x
  fan-center x = x , rx x

  cofan-center : ∀ x → cofan x
  cofan-center x = x , rx x
```

### Edge vocabulary

An edge family may reverse edges (`involutive`) or compose them (`transitive`).

```agda
  involutive : Type (v ⊔ e)
  involutive = ∀ {x y} → edge x y → edge y x

  transitive : Type (v ⊔ e)
  transitive = ∀ {x y z} → edge x y → edge y z → edge x z
```

### Univalence

A reflexive graph is *univalent* when every fan is a proposition: there is at
most one edge out of each vertex up to its target. This is the reflexive-graph
form of the identity-of-fibres principle.

```agda
  is-univalent : Type (v ⊔ e)
  is-univalent = ∀ x → is-prop (fan x)

  is-univalent-op : Type (v ⊔ e)
  is-univalent-op = ∀ y → is-prop (cofan y)
```

### Paths to edges

Reflexivity transports along a path of vertices to an edge, so every identity
of vertices induces an edge.

```agda
  to-edge : ∀ {x y} → x ≡ y → edge x y
  to-edge {x} p = transport (λ i → edge x (p i)) (rx x)
```

### The opposite graph

Reversing edges and keeping reflexivity yields the opposite reflexive graph.

```agda
  op : reflexive-graph v e
  op .vtx = vtx
  op .edge x y = edge y x
  op .rx = rx
```

### Consequences of univalence

When the graph is univalent, fans are contractible and edges become a
proper groupoid: an edge is recovered as an identity of vertices,
edges concatenate, and edges invert.

```agda
  module univalence (univ : is-univalent) where
    fan-contr : ∀ x → is-contr (fan x)
    fan-contr x = prop-inhabited→is-contr (univ x) (fan-center x)

    to-id : (x y : vtx) → edge x y → x ≡ y
    to-id x y p = ap fst (univ x (fan-center x) (y , p))

    concat : (x y z : vtx) → edge x y → edge y z → edge x z
    concat x y z p q = to-edge (to-id x y p ∙ to-id y z q)

    inv : (x y : vtx) → edge x y → edge y x
    inv x y p = to-edge (sym (to-id x y p))

  record hom {v' e'} (H : reflexive-graph v' e') : Type (v ⊔ v' ⊔ e ⊔ e') where
    private module H = reflexive-graph H
    field
      vmap : vtx → H.vtx
      emap : (x y : vtx) → edge x y → H.edge (vmap x) (vmap y)
      pres-rx : (x : vtx) → emap x x (rx x) ≡ H.rx (vmap x)
```

### Displayed reflexive graphs over `G`

Operations keyed on a displayed reflexive graph `D` over `G` — the total, its
opposite, the components, and the fibration conditions — belong to the same
interface: instantiating `rx G` supplies all of them for a fixed base.

The *total opposite* reverses the displayed edges of `D`, giving a displayed
graph over the opposite base `rx.op G`. It is not the naive opposite of a
displayed graph — that would lie over the same base, and does not exist in
general, just as Bénabou's opposites are defined only for displayed categories
that are fibrations (Sterling 15).

It is instead the reindexing realising opposition on the total: `rx.op
(total D)` is `total (total-op D)`. The operation is definitionally
involutive, `total-op (total-op D) ≡ D`, so no involution law is
stated.

The *component* of `D` at `x` is the reflexive graph of displayed
vertices over `x`, with edges lying over `rx x`. `D` is a *covariant
fibration* when every base edge, out of a fixed displayed source,
lifts to a contractible space of displayed targets, and a
*contravariant fibration* when the dual holds into a fixed target;
each contractible lift names a pushforward or pullback with its
lifting edge.

Following Sterling, *Reflexive Graph Lenses*, § "Duality involution for
reflexive graphs".

```agda
  module _ {v' e'} (D : reflexive-graphᴰ v' e' G) where
    private
      module D = reflexive-graphᴰ D

    total : reflexive-graph (v ⊔ v') (e ⊔ e')
    total .reflexive-graph.vtx                  = Σ x ∶ vtx , D.vtx x
    total .reflexive-graph.edge (x , u) (y , w) = Σ p ∶ edge x y , D.edge x y p u w
    total .reflexive-graph.rx (x , u)           = rx x , D.rx u

    total-op : reflexive-graphᴰ v' e' op
    total-op .reflexive-graphᴰ.vtx        = D.vtx
    total-op .reflexive-graphᴰ.edge x y p u w = D.edge y x p w u
    total-op .reflexive-graphᴰ.rx u       = D.rx u

    component : vfam v' e'
    component x .reflexive-graph.vtx      = D.vtx x
    component x .reflexive-graph.edge u w = D.edge x x (rx x) u w
    component x .reflexive-graph.rx u     = D.rx u
```

A *section* of `D` chooses a displayed vertex over every base vertex
and a displayed edge over every base edge, agreeing with displayed
reflexivity at the chosen edges. It is the displayed form of `hom`,
field for field, and the constant display below exhibits that: a
section of `constant S` is a graph morphism into `S`.

```agda
    record section : Type (v ⊔ v' ⊔ e ⊔ e') where
      field
        vmap    : (x : vtx) → D.vtx x
        emap    : (x y : vtx) (p : edge x y) → D.edge x y p (vmap x) (vmap y)
        pres-rx : (x : vtx) → emap x x (rx x) ≡ D.rx (vmap x)

    is-cov-fibration : Type (v ⊔ v' ⊔ e ⊔ e')
    is-cov-fibration =
      ∀ x y (p : edge x y) (u : D.vtx x) → is-contr (Σ w ∶ D.vtx y , D.edge x y p u w)

    is-ctrv-fibration : Type (v ⊔ v' ⊔ e ⊔ e')
    is-ctrv-fibration =
      ∀ x y (p : edge x y) (w : D.vtx y) → is-contr (Σ u ∶ D.vtx x , D.edge x y p u w)

    module cov-fibration (fib : is-cov-fibration) where
      push : (x y : vtx) → edge x y → D.vtx x → D.vtx y
      push x y p u = fib x y p u .center .fst

      lift : (x y : vtx) (p : edge x y) (u : D.vtx x) → D.edge x y p u (push x y p u)
      lift x y p u = fib x y p u .center .snd

      lift-unique
        : (x y : vtx) (p : edge x y) (u : D.vtx x) (w : D.vtx y) (e : D.edge x y p u w)
        → (push x y p u , lift x y p u) ≡ (w , e)
      lift-unique x y p u w e = fib x y p u .paths (w , e)

    module ctrv-fibration (fib : is-ctrv-fibration) where
      pull : (x y : vtx) → edge x y → D.vtx y → D.vtx x
      pull x y p w = fib x y p w .center .fst

      colift : (x y : vtx) (p : edge x y) (w : D.vtx y) → D.edge x y p (pull x y p w) w
      colift x y p w = fib x y p w .center .snd

      colift-unique : (x y : vtx) (p : edge x y) (w : D.vtx y) (u : D.vtx x) (e : D.edge x y p u w)
                    → (pull x y p w , colift x y p w) ≡ (u , e)
      colift-unique x y p w u e = fib x y p w .paths (u , e)

  binary-product : ∀ {w z} (H : reflexive-graph w z) → reflexive-graph (v ⊔ w) (e ⊔ z)
  binary-product H .reflexive-graph.vtx = vtx × reflexive-graph.vtx H
  binary-product H .reflexive-graph.edge (a , b) (c , d) = edge a c × reflexive-graph.edge H b d
  binary-product H .reflexive-graph.rx (a , b) = rx a , reflexive-graph.rx H b

  comprehension : ∀ {ℓ} (P : vtx → Type ℓ) → reflexive-graph (v ⊔ ℓ) e
  comprehension P .reflexive-graph.vtx = Σ x ∶ vtx , P x
  comprehension P .reflexive-graph.edge (x , _) (y , _) = edge x y
  comprehension P .reflexive-graph.rx (x , _) = rx x

  constant : ∀ {w z} (S : reflexive-graph w z) → disp w z
  constant S .reflexive-graphᴰ.vtx _      = reflexive-graph.vtx S
  constant S .reflexive-graphᴰ.edge _ _ _ u v = reflexive-graph.edge S u v
  constant S .reflexive-graphᴰ.rx u       = reflexive-graph.rx S u

  const-section : ∀ {w z} {S : reflexive-graph w z} → section (constant S) → hom S
  const-section s .hom.vmap    = section.vmap    s
  const-section s .hom.emap    = section.emap    s
  const-section s .hom.pres-rx = section.pres-rx s

  section-const : ∀ {w z} {S : reflexive-graph w z} → hom S → section (constant S)
  section-const f .section.vmap    = hom.vmap f
  section-const f .section.emap    = hom.emap f
  section-const f .section.pres-rx = hom.pres-rx f

  const-section-inv : ∀ {w z} {S : reflexive-graph w z} (f : hom S)
                    → const-section (section-const f) ≡ f
  const-section-inv _ = refl

  section-const-inv : ∀ {w z} {S : reflexive-graph w z} (s : section (constant S))
                    → section-const (const-section s) ≡ s
  section-const-inv _ = refl

  constant-section≃hom : ∀ {w z} (S : reflexive-graph w z) → section (constant S) ≃ hom S
  constant-section≃hom S =
    Core.Equiv.iso→equiv const-section section-const section-const-inv const-section-inv
```

The *discrete* reflexive graph on a type takes identifications as edges; the
*codiscrete* one takes a single edge everywhere.

```agda
discrete : ∀ {ℓ} → Type ℓ → reflexive-graph ℓ ℓ
discrete A .reflexive-graph.vtx      = A
discrete A .reflexive-graph.edge x y = x ≡ y
discrete A .reflexive-graph.rx x     = refl

codiscrete : ∀ {ℓ} → Type ℓ → reflexive-graph ℓ 0ℓ
codiscrete A .reflexive-graph.vtx      = A
codiscrete A .reflexive-graph.edge _ _ = ⊤
codiscrete A .reflexive-graph.rx _     = tt
```

The *image* of a family of types is the reflexive graph on the index type whose
edges are the equivalences between fibres, reflexivity being the identity
equivalence. A family is *univalent* — a *universe* when it is closed under type
formers — when its image is a path object.

```agda
image : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') → reflexive-graph ℓ ℓ'
image {A = A} B .reflexive-graph.vtx      = A
image {A = A} B .reflexive-graph.edge x y = B x ≃ B y
image {A = A} B .reflexive-graph.rx _     = aut

is-univalent-family : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ ⊔ ℓ')
is-univalent-family B = rx.is-univalent (image B)
```

A family of reflexive graphs is a family of *path objects* when each member is
one. The condition speaks about the `rx` interface of the members rather than of
any ambient base, so it stands outside that interface.

```agda
is-path-objects : ∀ {ℓ w z} {A : Type ℓ} → dep-rx w z A → Type (ℓ ⊔ w ⊔ z)
is-path-objects B = ∀ x → rx.is-univalent (B x)
```

A displayed reflexive graph is *displayed-univalent* when its family of
components is a family of path objects — the same condition, applied to the
`component` operation, so it too stands outside `rx`.

```agda
is-displayed-univalent
  : ∀ {v e v' e'} {G : reflexive-graph v e} → rx.disp G v' e' → Type (v ⊔ v' ⊔ e')
is-displayed-univalent {G = G} D = is-path-objects (rx.component G D)
```
