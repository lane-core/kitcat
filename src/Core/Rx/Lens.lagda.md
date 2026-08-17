Lenses of reflexive graphs over a base `G`: a family of reflexive graphs `B x`
equipped with transport along base edges. An *oplax covariant* lens transports
forward (`push`) with an oplax unitor; a *lax contravariant* lens transports
backward (`pull`) with a lax unitor. Each has a display recovering a displayed
reflexive graph over `G`, and the two are dual under the total opposite.

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Core.Rx.Lens where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Kan using (is-contr→is-prop)
open import Core.Equiv
open import Core.HLevel.Base using (Π-is-prop; Σ-is-prop; is-prop-equiv)
open import Core.Transport.Base using (transport)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.Rx.Type
open import Core.Rx.Base
open import Core.Rx.Properties

module _ {v e w z} (G : reflexive-graph v e) (B : rx.vfam G w z) where
  private
    module G = reflexive-graph G
    module B x = reflexive-graph (B x)
```

## Oplax covariant lenses

`push` transports a displayed vertex forward along a base edge; the oplax unitor
is an edge from the pushforward along reflexivity back to the vertex. The display
sends a displayed edge over `p` to a vertical edge out of the pushforward.

```agda

  private
    push : Type (v ⊔ w ⊔ e)
    push = (x y : G.vtx) → G.edge x y → B.vtx x → B.vtx y

  oplax-unitor : push → Type (v ⊔ w ⊔ z)
  oplax-unitor P = ∀ {x} (u : B.vtx x) → B.edge x (P x x (G.rx x) u) u

  universal-push : push → Type (v ⊔ w ⊔ e ⊔ z)
  universal-push P = (x y : G.vtx) (p : G.edge x y) (u : B.vtx x)
                   → is-prop (Σ q ∶ B.vtx y , B.edge y (P x y p u) q)

  record oplax-cov-lens : Type (v ⊔ w ⊔ e ⊔ z) where
    field
      has-push   : push
      has-unitor : oplax-unitor has-push

    display : rx.disp G w z
    display .reflexive-graphᴰ.vtx                = B.vtx
    display .reflexive-graphᴰ.edge x y p u q     = B.edge y (has-push x y p u) q
    display .reflexive-graphᴰ.rx u               = has-unitor u
```

Over a path object, a lens of path objects carries at most one covariant
structure. Distributing the structure over the base vertices leaves, at each `x`,
a pushforward defined on the fan of `x` paired with a unitor constraining it at
the centre. The fan is contractible, so the pushforward is its value there — an
endomorphism of `B.vtx x` — and the pair becomes the cofan of the identity in
`B.vtx x ⋔ B x`, a proposition since the cotensor is a path object.

```agda

  cov-lens-structure-is-prop : rx.is-univalent G → is-path-objects B
                             → is-prop oplax-cov-lens
  cov-lens-structure-is-prop G-univ B-univ = is-prop-equiv pointwise (Π-is-prop local-is-prop)
    where
    local : G.vtx → Type (v ⊔ w ⊔ e ⊔ z)
    local x = Σ Φ ∶ (∀ y (p : G.edge x y) → B.vtx x → B.vtx y)
            , (∀ u → B.edge x (Φ x (G.rx x) u) u)

    pointwise : oplax-cov-lens ≃ (∀ x → local x)
    pointwise = iso→equiv fwd bwd (λ _ → refl) (λ _ → refl)
      where
      fwd : oplax-cov-lens → ∀ x → local x
      fwd L x = (λ y p → oplax-cov-lens.has-push L x y p) , oplax-cov-lens.has-unitor L

      bwd : (∀ x → local x) → oplax-cov-lens
      bwd F .oplax-cov-lens.has-push x y p = F x .fst y p
      bwd F .oplax-cov-lens.has-unitor {x} = F x .snd

    local-is-prop : ∀ x → is-prop (local x)
    local-is-prop x = is-prop-equiv collapse endo-cofan-prop
      where
      endo : Type w
      endo = B.vtx x → B.vtx x

      unitor : endo → Type (w ⊔ z)
      unitor Φ = ∀ u → B.edge x (Φ u) u

      fan-contr : is-contr (rx.fan G x)
      fan-contr = prop-inhabited→is-contr (G-univ x) (rx.fan-center G x)

      fan-uncurry : (∀ y (p : G.edge x y) → B.vtx x → B.vtx y)
                  ≃ ((c : rx.fan G x) → B.vtx x → B.vtx (fst c))
      fan-uncurry = iso→equiv (λ Φ c → Φ (fst c) (snd c)) (λ Ψ y p → Ψ (y , p))
                              (λ _ → refl) (λ _ → refl)

      at-center : ((c : rx.fan G x) → B.vtx x → B.vtx (fst c)) ≃ endo
      at-center = Π-contr-dom fan-contr

      collapse : local x ≃ (Σ Φ ∶ endo , unitor Φ)
      collapse = Σ-equiv-fst {P = λ Ψ → unitor (at-center .fst Ψ)} fan-uncurry
               ∙e Σ-equiv-fst {P = unitor} at-center

      endo-cofan-prop : is-prop (Σ Φ ∶ endo , unitor Φ)
      endo-cofan-prop =
        po.is-univalent→op (rx.cotensor (B x) (B.vtx x))
          (cotensor-path-object (B x) (B.vtx x) (B-univ x)) (λ u → u)

```

## Lax contravariant lenses

The dual: `pull` transports backward, the lax unitor is an edge from the vertex
to its pullback along reflexivity, and the display sends a displayed edge over
`p` to a vertical edge into the pullback.

```agda

  private
    pull : Type (v ⊔ w ⊔ e)
    pull = (x y : G.vtx) → G.edge x y → B.vtx y → B.vtx x

  lax-unitor : pull → Type (v ⊔ w ⊔ z)
  lax-unitor P = ∀ {x} (u : B.vtx x) → B.edge x u (P x x (G.rx x) u)

  universal-pull : pull → Type (v ⊔ w ⊔ e ⊔ z)
  universal-pull P = (x y : G.vtx) (p : G.edge x y) (u : B.vtx y)
                   → is-prop (Σ q ∶ B.vtx x , B.edge x q (P x y p u))

  record lax-ctrv-lens : Type (v ⊔ w ⊔ e ⊔ z) where
    field
      has-pull   : pull
      has-unitor : lax-unitor has-pull

    display : rx.disp G w z
    display .reflexive-graphᴰ.vtx                = B.vtx
    display .reflexive-graphᴰ.edge x y p u q     = B.edge x u (has-pull x y p q)
    display .reflexive-graphᴰ.rx u               = has-unitor u
```

The dual uniqueness statement. The same collapse leaves the fan — rather than the
cofan — of the identity, so the cotensor's own path-object structure suffices.

```agda

  ctrv-lens-structure-is-prop : rx.is-univalent G → is-path-objects B
                              → is-prop lax-ctrv-lens
  ctrv-lens-structure-is-prop G-univ B-univ = is-prop-equiv pointwise (Π-is-prop local-is-prop)
    where
    local : G.vtx → Type (v ⊔ w ⊔ e ⊔ z)
    local x = Σ Φ ∶ (∀ y (p : G.edge x y) → B.vtx y → B.vtx x)
            , (∀ u → B.edge x u (Φ x (G.rx x) u))

    pointwise : lax-ctrv-lens ≃ (∀ x → local x)
    pointwise = iso→equiv fwd bwd (λ _ → refl) (λ _ → refl)
      where
      fwd : lax-ctrv-lens → ∀ x → local x
      fwd M x = (λ y p → lax-ctrv-lens.has-pull M x y p) , lax-ctrv-lens.has-unitor M

      bwd : (∀ x → local x) → lax-ctrv-lens
      bwd F .lax-ctrv-lens.has-pull x y p = F x .fst y p
      bwd F .lax-ctrv-lens.has-unitor {x} = F x .snd

    local-is-prop : ∀ x → is-prop (local x)
    local-is-prop x = is-prop-equiv collapse endo-fan-prop
      where
      endo : Type w
      endo = B.vtx x → B.vtx x

      unitor : endo → Type (w ⊔ z)
      unitor Φ = ∀ u → B.edge x u (Φ u)

      fan-contr : is-contr (rx.fan G x)
      fan-contr = prop-inhabited→is-contr (G-univ x) (rx.fan-center G x)

      fan-uncurry : (∀ y (p : G.edge x y) → B.vtx y → B.vtx x)
                  ≃ ((c : rx.fan G x) → B.vtx (fst c) → B.vtx x)
      fan-uncurry = iso→equiv (λ Φ c → Φ (fst c) (snd c)) (λ Ψ y p → Ψ (y , p))
                              (λ _ → refl) (λ _ → refl)

      at-center : ((c : rx.fan G x) → B.vtx (fst c) → B.vtx x) ≃ endo
      at-center = Π-contr-dom fan-contr

      collapse : local x ≃ (Σ Φ ∶ endo , unitor Φ)
      collapse = Σ-equiv-fst {P = λ Ψ → unitor (at-center .fst Ψ)} fan-uncurry
               ∙e Σ-equiv-fst {P = unitor} at-center

      endo-fan-prop : is-prop (Σ Φ ∶ endo , unitor Φ)
      endo-fan-prop = cotensor-path-object (B x) (B.vtx x) (B-univ x) (λ u → u)
```

## Unbiased dependent lenses

The common generalisation, with the family indexed by base *edges*. Left and
right injections carry the diagonal components `B (G.rx x)` and `B (G.rx y)` into
the central component `B p`; the mid unitor relates the two injections along
reflexivity, and a lax unitor sends a vertex to its right injection.

```agda
module _ {v e w z} (G : reflexive-graph v e) (B : rx.efam G w z) where
  private
    module G = reflexive-graph G
    module mid {x y} (p : G.edge x y) = reflexive-graph (B x y p)

    left-injective : Type (v ⊔ w ⊔ e)
    left-injective = (x y : G.vtx) (p : G.edge x y) → mid.vtx (G.rx x) → mid.vtx p

    right-injective : Type (v ⊔ w ⊔ e)
    right-injective = (x y : G.vtx) (p : G.edge x y) → mid.vtx (G.rx y) → mid.vtx p

    mid-unitor : left-injective → right-injective → Type (v ⊔ w ⊔ z)
    mid-unitor L R = (x : G.vtx) (u : mid.vtx (G.rx x)) → mid.edge (G.rx x) (L x x (G.rx x) u) (R x x (G.rx x) u)

    right-lax-unitor : right-injective → Type (v ⊔ w ⊔ z)
    right-lax-unitor R = (x : G.vtx) (u : mid.vtx (G.rx x)) → mid.edge (G.rx x) u (R x x (G.rx x) u)

  record unbiased-lens : Type (v ⊔ e ⊔ w ⊔ z) where
    field
      linj    : left-injective
      rinj    : right-injective
      munitor : mid-unitor linj rinj
      runitor : right-lax-unitor rinj

    display : rx.disp G w z
    display .reflexive-graphᴰ.vtx x           = mid.vtx (G.rx x)
    display .reflexive-graphᴰ.edge x y p u v  = mid.edge p (linj x y p u) (rinj x y p v)
    display .reflexive-graphᴰ.rx {x} u        = munitor x u
```

Over a path object the two path-object conditions on an edge-indexed family
agree. Reflexivity is the centre of the contractible fan of `x`, so a path-object
structure on the diagonal component transports along the fan to the component at
any edge out of `x`.

```agda
  component-path-object : rx.is-univalent G → is-path-objects (rx.diag G B)
                        → (x y : G.vtx) (p : G.edge x y) → rx.is-univalent (B x y p)
  component-path-object G-univ B-univ x y p =
    transport (λ i → rx.is-univalent (B x (fst (fan-path i)) (snd (fan-path i)))) (B-univ x)
    where
    fan-path : rx.fan-center G x ≡ (y , p)
    fan-path = G-univ x (rx.fan-center G x) (y , p)
```

Uniqueness again, with the diagonal components taken to be path objects. Both
injections collapse to endomorphisms of `mid.vtx (G.rx x)` at the centre of the
fan of `x`. The lax unitor then pairs the right injection into the fan of the
identity in `mid.vtx (G.rx x) ⋔ B (G.rx x)`, and that fan is contractible, so the
mid unitor is left as the cofan of the identity.

```agda
  unb-lens-structure-is-prop : rx.is-univalent G → is-path-objects (rx.diag G B)
                             → is-prop unbiased-lens
  unb-lens-structure-is-prop G-univ B-univ = is-prop-equiv pointwise (Π-is-prop local-is-prop)
    where
    local : G.vtx → Type (v ⊔ w ⊔ e ⊔ z)
    local x = Σ Φ ∶ (∀ y (p : G.edge x y) → mid.vtx (G.rx x) → mid.vtx p)
            , Σ Ψ ∶ (∀ y (p : G.edge x y) → mid.vtx (G.rx y) → mid.vtx p)
            , ((∀ u → mid.edge (G.rx x) (Φ x (G.rx x) u) (Ψ x (G.rx x) u))
               × (∀ u → mid.edge (G.rx x) u (Ψ x (G.rx x) u)))

    pointwise : unbiased-lens ≃ (∀ x → local x)
    pointwise = iso→equiv fwd bwd (λ _ → refl) (λ _ → refl)
      where
      fwd : unbiased-lens → ∀ x → local x
      fwd L x = (λ y p → unbiased-lens.linj L x y p)
              , (λ y p → unbiased-lens.rinj L x y p)
              , (unbiased-lens.munitor L x , unbiased-lens.runitor L x)

      bwd : (∀ x → local x) → unbiased-lens
      bwd F .unbiased-lens.linj    x y p = F x .fst y p
      bwd F .unbiased-lens.rinj    x y p = F x .snd .fst y p
      bwd F .unbiased-lens.munitor x     = F x .snd .snd .fst
      bwd F .unbiased-lens.runitor x     = F x .snd .snd .snd

    local-is-prop : ∀ x → is-prop (local x)
    local-is-prop x = is-prop-equiv collapse endo-cofan-prop
      where
      diagonal : reflexive-graph w z
      diagonal = B x x (G.rx x)

      endo : Type w
      endo = mid.vtx (G.rx x) → mid.vtx (G.rx x)

      idf : endo
      idf u = u

      unitors : endo → endo → Type (w ⊔ z)
      unitors Φ Ψ = (∀ u → mid.edge (G.rx x) (Φ u) (Ψ u))
                    × (∀ u → mid.edge (G.rx x) u (Ψ u))

      fan-contr : is-contr (rx.fan G x)
      fan-contr = prop-inhabited→is-contr (G-univ x) (rx.fan-center G x)

      left-uncurry : (∀ y (p : G.edge x y) → mid.vtx (G.rx x) → mid.vtx p)
                   ≃ ((c : rx.fan G x) → mid.vtx (G.rx x) → mid.vtx (snd c))
      left-uncurry = iso→equiv (λ Φ c → Φ (fst c) (snd c)) (λ Φ y p → Φ (y , p))
                               (λ _ → refl) (λ _ → refl)

      left-at-center : ((c : rx.fan G x) → mid.vtx (G.rx x) → mid.vtx (snd c)) ≃ endo
      left-at-center = Π-contr-dom fan-contr

      right-uncurry : (∀ y (p : G.edge x y) → mid.vtx (G.rx y) → mid.vtx p)
                    ≃ ((c : rx.fan G x) → mid.vtx (G.rx (fst c)) → mid.vtx (snd c))
      right-uncurry = iso→equiv (λ Ψ c → Ψ (fst c) (snd c)) (λ Ψ y p → Ψ (y , p))
                                (λ _ → refl) (λ _ → refl)

      right-at-center : ((c : rx.fan G x) → mid.vtx (G.rx (fst c)) → mid.vtx (snd c)) ≃ endo
      right-at-center = Π-contr-dom fan-contr

      left-endo : (∀ y (p : G.edge x y) → mid.vtx (G.rx x) → mid.vtx p) ≃ endo
      left-endo = left-uncurry ∙e left-at-center

      right-endo : (∀ y (p : G.edge x y) → mid.vtx (G.rx y) → mid.vtx p) ≃ endo
      right-endo = right-uncurry ∙e right-at-center

      cot : reflexive-graph w (w ⊔ z)
      cot = rx.cotensor diagonal (mid.vtx (G.rx x))

      cot-univ : rx.is-univalent cot
      cot-univ = cotensor-path-object diagonal (mid.vtx (G.rx x)) (B-univ x)

      cot-fan-contr : is-contr (rx.fan cot idf)
      cot-fan-contr = prop-inhabited→is-contr (cot-univ idf) (rx.fan-center cot idf)

      collapse : local x ≃ rx.cofan cot idf
      collapse = Σ-equiv-snd (λ Φ → Σ-equiv-fst {P = unitors (left-endo .fst Φ)} right-endo)
               ∙e Σ-equiv-fst {P = λ Φ → Σ Ψ ∶ endo , unitors Φ Ψ} left-endo
               ∙e Σ-equiv-snd (λ _ → iso→equiv (λ (Ψ , m , r) → (Ψ , r) , m)
                                               (λ ((Ψ , r) , m) → Ψ , m , r)
                                               (λ _ → refl) (λ _ → refl))
               ∙e Σ-equiv-snd (λ _ → Σ-contr-fst cot-fan-contr)

      endo-cofan-prop : is-prop (rx.cofan cot idf)
      endo-cofan-prop = po.is-univalent→op cot cot-univ idf
```

When each `B x` is univalent — a *lens of path objects* — the covariant display
is univalent: its component fan at `u` is definitionally the fan of `B x` at the
pushforward, hence a proposition.

```agda
cov-disp-path-object : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z}
                     → (L : oplax-cov-lens G B) → is-path-objects B
                     → is-displayed-univalent (oplax-cov-lens.display L)
cov-disp-path-object {G = G} L B-univ x u =
  B-univ x (oplax-cov-lens.has-push L x x (reflexive-graph.rx G x) u)
```

The flattening operations are keyed on a lens over one base, recovered from the
lens along with its family.

```agda

module _ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z} where
  private
    module G = reflexive-graph G
    module B x = reflexive-graph (B x)
```

## Flattening

A lens reparameterises its base: an edge of the *flattening* carries a base edge
together with a transport of the fibres and a comparison with the lens'. The
identity function and the unitor supply the reflexive edge, so the unit law holds
on the nose over the flattened base.

```agda
  cov-flatten : oplax-cov-lens G B → reflexive-graph v (w ⊔ e ⊔ z)
  cov-flatten L .reflexive-graph.vtx = G.vtx
  cov-flatten L .reflexive-graph.edge x y =
    Σ p ∶ G.edge x y , Σ q ∶ (B.vtx x → B.vtx y)
      , (∀ u → B.edge y (oplax-cov-lens.has-push L x y p u) (q u))
  cov-flatten L .reflexive-graph.rx x =
    G.rx x , (λ u → u) , oplax-cov-lens.has-unitor L

  ctrv-flatten : lax-ctrv-lens G B → reflexive-graph v (w ⊔ e ⊔ z)
  ctrv-flatten M .reflexive-graph.vtx = G.vtx
  ctrv-flatten M .reflexive-graph.edge x y =
    Σ p ∶ G.edge x y , Σ q ∶ (B.vtx y → B.vtx x)
      , (∀ u → B.edge x (q u) (lax-ctrv-lens.has-pull M x y p u))
  ctrv-flatten M .reflexive-graph.rx x =
    G.rx x , (λ u → u) , lax-ctrv-lens.has-unitor M
```

Flattening a lens of path objects over a path object gives a path object. The
fan reassociates into the base fan paired with the fan — for the contravariant
lens, the cofan — of the transported fibre in `B.vtx x ⋔ B y`, which the
cotensor's path-object structure makes contractible.

```agda
  cov-flatten-path-object : (L : oplax-cov-lens G B)
                          → rx.is-univalent G → is-path-objects B
                          → rx.is-univalent (cov-flatten L)
  cov-flatten-path-object L G-univ B-univ x =
    is-prop-equiv reassoc (Σ-is-prop (G-univ x) fibre-prop)
    where
    reassoc : rx.fan (cov-flatten L) x
            ≃ (Σ c ∶ rx.fan G x
                 , rx.fan (rx.cotensor (B (fst c)) (B.vtx x))
                          (oplax-cov-lens.has-push L x (fst c) (snd c)))
    reassoc = iso→equiv (λ (y , p , q , h) → (y , p) , (q , h))
                        (λ ((y , p) , (q , h)) → y , p , q , h)
                        (λ _ → refl) (λ _ → refl)

    fibre-prop : ∀ c → is-prop (rx.fan (rx.cotensor (B (fst c)) (B.vtx x))
                                       (oplax-cov-lens.has-push L x (fst c) (snd c)))
    fibre-prop c = cotensor-path-object (B (fst c)) (B.vtx x) (B-univ (fst c)) _

  ctrv-flatten-path-object : (M : lax-ctrv-lens G B)
                           → rx.is-univalent G → is-path-objects B
                           → rx.is-univalent (ctrv-flatten M)
  ctrv-flatten-path-object M G-univ B-univ x =
    is-prop-equiv reassoc (Σ-is-prop (G-univ x) fibre-prop)
    where
    reassoc : rx.fan (ctrv-flatten M) x
            ≃ (Σ c ∶ rx.fan G x
                 , rx.cofan (rx.cotensor (B x) (B.vtx (fst c)))
                            (lax-ctrv-lens.has-pull M x (fst c) (snd c)))
    reassoc = iso→equiv (λ (y , p , q , h) → (y , p) , (q , h))
                        (λ ((y , p) , (q , h)) → y , p , q , h)
                        (λ _ → refl) (λ _ → refl)

    fibre-prop : ∀ c → is-prop (rx.cofan (rx.cotensor (B x) (B.vtx (fst c)))
                                         (lax-ctrv-lens.has-pull M x (fst c) (snd c)))
    fibre-prop c =
      po.is-univalent→op (rx.cotensor (B x) (B.vtx (fst c)))
        (cotensor-path-object (B x) (B.vtx (fst c)) (B-univ x)) _
```

## Total opposite

The total opposite carries an oplax covariant lens over `G` to a lax
contravariant lens over `rx.op G`: the fibres become their opposites, and `pull`
with its unitor are `push` with its unitor read against the reversed edges. Its
display is the total opposite of the covariant display, definitionally.

```agda
tot-op-lens
  : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z}
  → oplax-cov-lens G B → lax-ctrv-lens (rx.op G) (rx.op ∘ B)
tot-op-lens L .lax-ctrv-lens.has-pull x y p   = oplax-cov-lens.has-push   L y x p
tot-op-lens L .lax-ctrv-lens.has-unitor = oplax-cov-lens.has-unitor L

display-of-tot-op
  : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z} (L : oplax-cov-lens G B)
  → lax-ctrv-lens.display (tot-op-lens L) ≡ rx.total-op G (oplax-cov-lens.display L)
display-of-tot-op L = refl
```

The contravariant dual, and the univalence of a contravariant display of a lens
of path objects — routed through the covariant result along the total opposite.

```agda
tot-op-lens⁻
  : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z}
  → lax-ctrv-lens G B → oplax-cov-lens (rx.op G) (λ x → rx.op (B x))
tot-op-lens⁻ M .oplax-cov-lens.has-push x y p   = lax-ctrv-lens.has-pull   M y x p
tot-op-lens⁻ M .oplax-cov-lens.has-unitor = lax-ctrv-lens.has-unitor M

ctrv-disp-path-object : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z}
                      → (M : lax-ctrv-lens G B) → is-path-objects B
                      → is-displayed-univalent (lax-ctrv-lens.display M)
ctrv-disp-path-object {G = G} {B} M B-univ x =
  po.is-univalent-op→ (rx.component G (lax-ctrv-lens.display M) x)
    (cov-disp-path-object (tot-op-lens⁻ M)
                 (λ x' → po.is-univalent→op (B x') (B-univ x')) x)
```

## From biased to unbiased

Both biased lenses generalise to unbiased dependent lenses, with the biased
display recovered as the unbiased display definitionally. The covariant family
sits over the target, the contravariant over the source.

```agda
cov-lens-to-unbiased : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z}
                     → oplax-cov-lens G B → unbiased-lens G (λ _ y _ → B y)
cov-lens-to-unbiased L .unbiased-lens.linj x y p u        = oplax-cov-lens.has-push   L x y p u
cov-lens-to-unbiased L .unbiased-lens.rinj x y p u        = u
cov-lens-to-unbiased L .unbiased-lens.munitor x u         = oplax-cov-lens.has-unitor L u
cov-lens-to-unbiased {B = B} L .unbiased-lens.runitor x u = reflexive-graph.rx (B x) u

ctrv-lens-to-unbiased : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.vfam G w z}
                      → lax-ctrv-lens G B → unbiased-lens G (λ x _ _ → B x)
ctrv-lens-to-unbiased M .unbiased-lens.linj x y p u  = u
ctrv-lens-to-unbiased M .unbiased-lens.rinj x y p u  = lax-ctrv-lens.has-pull   M x y p u
ctrv-lens-to-unbiased M .unbiased-lens.munitor x u   = lax-ctrv-lens.has-unitor M u
ctrv-lens-to-unbiased M .unbiased-lens.runitor x u   = lax-ctrv-lens.has-unitor M u
```

When each diagonal component is univalent, the unbiased display is univalent.
The right lax unitor makes `rinj` at the reflexive edge homotopic to the
identity — hence an equivalence — so the component fan at `u` is definitionally
the contractible fibre of `rinj` over the left injection.

```agda
unb-disp-path-object
  : ∀ {v e w z} {G : reflexive-graph v e} {B : rx.efam G w z}
    (L : unbiased-lens G B) → is-path-objects (rx.diag G B)
  → is-displayed-univalent (unbiased-lens.display L)
unb-disp-path-object {G = G} {B} L B-univ x u = is-contr→is-prop (is-contr-equiv fan≃fibre fibre-contr)
  where
  module G = reflexive-graph G
  F  = B x x (G.rx x)
  Fu = B-univ x
  rj = unbiased-lens.rinj L x x (G.rx x)
  a  = unbiased-lens.linj L x x (G.rx x) u

  H : ∀ v → rj v ≡ v
  H v = sym (esym (po.edge≃path F Fu) .fst (unbiased-lens.runitor L x v))

  rj-equiv : reflexive-graph.vtx F ≃ reflexive-graph.vtx F
  rj-equiv = iso→equiv rj (λ v → v) H H

  fan≃fibre : rx.fan (rx.component G (unbiased-lens.display L) x) u ≃ fiber rj a
  fan≃fibre = Σ-equiv-snd (λ v → esym (po.edge≃path F Fu) ∙e path-sym-equiv)

  fibre-contr : is-contr (fiber rj a)
  fibre-contr = rj-equiv .snd .eqv-fibers a
```
