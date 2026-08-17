Path objects classifying `U`-small graphs and reflexive graphs, after Sterling,
*Reflexive Graph Lenses*. Throughout, `(U , E)` is a univalent family, so its
image is a path object and identifications in `U` are equivalences of fibres.

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Core.Rx.Classify where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Equiv using (_≃_; Equiv)
open import Core.Data.Bool using (Bool)
open import Core.Data.Trunc using (∥_∥; squash)
open import Core.Rx.Type
open import Core.Rx.Base
open import Core.Rx.Properties
open import Core.Rx.Lens
open import Core.Rx.Poly

module _ {ℓ ℓ'} {U : Type ℓ} (E : U → Type ℓ') (U-univ : is-univalent-family E) where
  private
    𝒰 : reflexive-graph ℓ ℓ'
    𝒰 = image E
```

## Graphs

A `U`-small graph structure on `A : U` is a vertex of the cotensor
`E A ⋔ E A ⋔ 𝒰`. Reindexing an edge family along an equivalence of vertex types
is a lax contravariant lens: the pullback substitutes the equivalence into both
arguments, so pulling back along reflexivity returns the family unchanged and the
unitor is reflexivity itself.

```agda
  gph-on : dep-rx (ℓ ⊔ ℓ') ℓ' U
  gph-on A = rx.cotensor (rx.cotensor 𝒰 (E A)) (E A)

  gph-lens : lax-ctrv-lens 𝒰 gph-on
  gph-lens .lax-ctrv-lens.has-pull _ _ f Ed a b = Ed (f .fst a) (f .fst b)
  gph-lens .lax-ctrv-lens.has-unitor Ed = reflexive-graph.rx (gph-on _) Ed

  gph-on-path-objects : is-path-objects gph-on
  gph-on-path-objects A =
    cotensor-path-object (rx.cotensor 𝒰 (E A)) (E A) (cotensor-path-object 𝒰 (E A) U-univ)
```

The total of its display classifies `U`-small graphs: vertices are a carrier
together with an edge family, and edges are an equivalence of carriers together
with a fibrewise equivalence of edge families over it.

```agda
  Gph : reflexive-graph (ℓ ⊔ ℓ') ℓ'
  Gph = rx.total 𝒰 (lax-ctrv-lens.display gph-lens)

  Gph-path-object : rx.is-univalent Gph
  Gph-path-object =
    total-path-object (lax-ctrv-lens.display gph-lens) U-univ
      (ctrv-disp-path-object gph-lens gph-on-path-objects)
```

## Reflexive graphs

Reflexivity data are of mixed variance in the underlying graph, so neither biased
lens accommodates them; an unbiased dependent lens does. Over an edge of `Gph` a
reflexivity datum assigns a self-edge in the image of the vertex map, discretely.
The left injection carries a datum forward along the fibrewise equivalence, the
right injection reindexes one along the vertex map, and at reflexivity both are
the identity, so the two unitors are reflexivity.

```agda
  private
    module Gph = reflexive-graph Gph

  rx-on : (Gr₀ Gr₁ : Gph.vtx) → Gph.edge Gr₀ Gr₁ → reflexive-graph ℓ' ℓ'
  rx-on Gr₀ Gr₁ f =
    product (E (Gr₀ .fst)) λ a → discrete (E (Gr₁ .snd (f .fst .fst a) (f .fst .fst a)))

  rx-lens : unbiased-lens Gph rx-on
  rx-lens .unbiased-lens.linj Gr₀ Gr₁ f rxs = λ a → f .snd a a .fst (rxs a)
  rx-lens .unbiased-lens.rinj Gr₀ Gr₁ f rxs = λ a → rxs (f .fst .fst a)
  rx-lens .unbiased-lens.munitor _ _ = λ _ → refl
  rx-lens .unbiased-lens.runitor _ _ = λ _ → refl

  private
    rx-display : rx.disp Gph ℓ' ℓ'
    rx-display = unbiased-lens.display rx-lens

  RxGph : reflexive-graph (ℓ ⊔ ℓ') ℓ'
  RxGph = rx.total Gph rx-display

  RxGph-path-object : rx.is-univalent RxGph
  RxGph-path-object =
    total-path-object rx-display Gph-path-object
      (unb-disp-path-object rx-lens
        λ Gr → prod-path-object (E (Gr .fst)) (λ a → discrete (E (Gr .snd a a)))
                                λ a → disc-path-object _)
```

## Classifying covariant lenses

A `U`-small reflexive graph — a vertex of `RxGph` — is realised as an actual
reflexive graph. An edge of `RxGph` carries a vertex map and a fibrewise
equivalence of edges, projected out below.

```agda
  module _ {v e} (gA : reflexive-graph v e) where
    private
      module A = reflexive-graph gA
      module RxGph = reflexive-graph RxGph

    realize : RxGph.vtx → reflexive-graph ℓ' ℓ'
    realize gB .reflexive-graph.vtx      = E (gB .fst .fst)
    realize gB .reflexive-graph.edge a b = E (gB .fst .snd a b)
    realize gB .reflexive-graph.rx a     = gB .snd a

    vmap : (gB₀ gB₁ : RxGph.vtx) → RxGph.edge gB₀ gB₁
         → reflexive-graph.vtx (realize gB₀) → reflexive-graph.vtx (realize gB₁)
    vmap _ _ f = f .fst .fst .fst

    emap : (gB₀ gB₁ : RxGph.vtx) (f : RxGph.edge gB₀ gB₁) (a b : reflexive-graph.vtx (realize gB₀))
         → reflexive-graph.edge (realize gB₀) a b ≃ reflexive-graph.edge (realize gB₁) (vmap gB₀ gB₁ f a) (vmap gB₀ gB₁ f b)
    emap _ _ f = f .fst .snd
```

The base is `vtx gA ⋔ RxGph`: its vertices are `gA`-indexed families of small
reflexive graphs. A covariant lens datum over an edge `f` of that base is a
pushforward `Φ` along base edges together with an oplax-unitor comparison to the
vertex map of `f` at reflexivity.

```agda
    𝒜 : reflexive-graph (v ⊔ ℓ ⊔ ℓ') (v ⊔ ℓ')
    𝒜 = rx.cotensor RxGph A.vtx

    private module 𝒜 = reflexive-graph 𝒜

    CovLensStr : (gB₀ gB₁ : 𝒜.vtx) → 𝒜.edge gB₀ gB₁ → Type (v ⊔ e ⊔ ℓ')
    CovLensStr gB₀ gB₁ f =
      Σ Φ ∶ ((x y : A.vtx) → A.edge x y
               → reflexive-graph.vtx (realize (gB₀ x)) → reflexive-graph.vtx (realize (gB₁ y)))
          , (∀ x (u : reflexive-graph.vtx (realize (gB₀ x)))
               → reflexive-graph.edge (realize (gB₁ x)) (Φ x x (A.rx x) u) (vmap (gB₀ x) (gB₁ x) (f x) u))
```

The classifying construction is an unbiased dependent lens whose fibre at `f` is
the discrete graph on `CovLensStr f`. The injections transport the pushforward
and unitor along `f`'s vertex map and fibrewise edge equivalence; at reflexivity
these act by the identity, so both unit laws hold on the nose.

```agda
    lens-of-lenses : unbiased-lens 𝒜 (λ gB₀ gB₁ f → discrete (CovLensStr gB₀ gB₁ f))
    lens-of-lenses .unbiased-lens.linj gB₀ gB₁ f (Φ , Φ̂) =
        (λ x y p u → vmap (gB₀ y) (gB₁ y) (f y) (Φ x y p u))
      , (λ x u → emap (gB₀ x) (gB₁ x) (f x) (Φ x x (A.rx x) u) u .fst (Φ̂ x u))
    lens-of-lenses .unbiased-lens.rinj gB₀ gB₁ f (Φ , Φ̂) =
        (λ x y p u → Φ x y p (vmap (gB₀ x) (gB₁ x) (f x) u))
      , (λ x u → Φ̂ x (vmap (gB₀ x) (gB₁ x) (f x) u))
    lens-of-lenses .unbiased-lens.munitor _ _ = refl
    lens-of-lenses .unbiased-lens.runitor _ _ = refl

    cov-lens-over : reflexive-graph (v ⊔ e ⊔ ℓ ⊔ ℓ') (v ⊔ e ⊔ ℓ')
    cov-lens-over = rx.total 𝒜 (unbiased-lens.display lens-of-lenses)
```

## Classifying displayed reflexive graphs over a fixed base

A displayed-graph structure over `gA` is a displayed vertex family `B : vtx gA → U`
together with a displayed edge structure: over each base edge `p : x ~> y` and
displayed vertices `u`, `v`, a type of displayed edges. Reindexing the latter
along a fibrewise equivalence of displayed vertices is a lax contravariant lens
over `vtx gA ⋔ 𝒰`; its total classifies displayed-graph structures.

```agda
    dgph-base : reflexive-graph (v ⊔ ℓ) (v ⊔ ℓ')
    dgph-base = rx.cotensor 𝒰 A.vtx

    DGphIx : (A.vtx → U) → Type (v ⊔ e ⊔ ℓ')
    DGphIx B = Σ x ∶ A.vtx , Σ y ∶ A.vtx , Σ _ ∶ A.edge x y , (E (B x) × E (B y))

    DGphOn : reflexive-graph.vtx dgph-base → reflexive-graph (v ⊔ e ⊔ ℓ ⊔ ℓ') (v ⊔ e ⊔ ℓ')
    DGphOn B = product (DGphIx B) (λ _ → 𝒰)

    DGph-lens : lax-ctrv-lens dgph-base DGphOn
    DGph-lens .lax-ctrv-lens.has-pull _ _ f Ed (x , y , p , u , v) =
      Ed (x , y , p , f x .fst u , f y .fst v)
    DGph-lens .lax-ctrv-lens.has-unitor Ed = reflexive-graph.rx (DGphOn _) Ed

    DGph : reflexive-graph (v ⊔ e ⊔ ℓ ⊔ ℓ') (v ⊔ e ⊔ ℓ')
    DGph = rx.total dgph-base (lax-ctrv-lens.display DGph-lens)

    DGph-path-object : rx.is-univalent DGph
    DGph-path-object =
      total-path-object (lax-ctrv-lens.display DGph-lens)
        (cotensor-path-object 𝒰 A.vtx U-univ)
        (ctrv-disp-path-object DGph-lens
          λ B → prod-path-object (DGphIx B) (λ _ → 𝒰) (λ _ → U-univ))
```

Displayed reflexivity data are of mixed variance, so — as with `RxGph` — they are
classified by an unbiased dependent lens over the edges of `DGph`. Its fibre at `f`
assigns, discretely, a self-edge in the image of `f`'s vertex map. The injections
carry a datum forward along the fibrewise edge equivalence of `f` and reindex one
along its vertex map; both act by the identity at reflexivity.

```agda
    private module DGph = reflexive-graph DGph

    DRxOn : (gB₀ gB₁ : DGph.vtx) → DGph.edge gB₀ gB₁ → reflexive-graph (v ⊔ ℓ') (v ⊔ ℓ')
    DRxOn gB₀ gB₁ f =
      product (Σ x ∶ A.vtx , E (gB₀ .fst x))
        (λ (x , y) → discrete (E (gB₁ .snd (x , x , A.rx x , f .fst x .fst y , f .fst x .fst y))))

    DRx-lens : unbiased-lens DGph DRxOn
    DRx-lens .unbiased-lens.linj gB₀ gB₁ f rxs =
      λ (x , y) → f .snd (x , x , A.rx x , y , y) .fst (rxs (x , y))
    DRx-lens .unbiased-lens.rinj gB₀ gB₁ f rxs =
      λ (x , y) → rxs (x , f .fst x .fst y)
    DRx-lens .unbiased-lens.munitor _ _ = λ _ → refl
    DRx-lens .unbiased-lens.runitor _ _ = λ _ → refl

    DRxGphOver : reflexive-graph (v ⊔ e ⊔ ℓ ⊔ ℓ') (v ⊔ e ⊔ ℓ')
    DRxGphOver = rx.total DGph (unbiased-lens.display DRx-lens)

    DRxGphOver-path-object : rx.is-univalent DRxGphOver
    DRxGphOver-path-object =
      total-path-object (unbiased-lens.display DRx-lens) DGph-path-object
        (unb-disp-path-object DRx-lens
          λ gB → prod-path-object (Σ x ∶ A.vtx , E (gB .fst x))
                   (λ (x , y) → discrete (E (gB .snd (x , x , A.rx x , y , y))))
                   (λ _ → disc-path-object _))
```

## Magmas

The reflexive graph of `U`-small magmas is the total of a displayed reflexive
graph `BinOp` over `𝒰` — a binary operation on the carrier, with edges the
homomorphism condition. `BinOp` arises from neither biased lens but from an
unbiased one on the discrete family of operation carriers: the injections
transport an operation forward along the vertex equivalence and reindex one
against it, agreeing on the nose at reflexivity.

```agda
  binop± : rx.efam 𝒰 ℓ' ℓ'
  binop± A B f = product (E A × E A) (λ _ → discrete (E B))

  binop-lens : unbiased-lens 𝒰 binop±
  binop-lens .unbiased-lens.linj A B f ⊗A = λ (x , y) → f .fst (⊗A (x , y))
  binop-lens .unbiased-lens.rinj A B f ⊗B = λ (x , y) → ⊗B (f .fst x , f .fst y)
  binop-lens .unbiased-lens.munitor _ _ = λ _ → refl
  binop-lens .unbiased-lens.runitor _ _ = λ _ → refl

  BinOp : rx.disp 𝒰 ℓ' ℓ'
  BinOp = unbiased-lens.display binop-lens

  Magma : reflexive-graph (ℓ ⊔ ℓ') ℓ'
  Magma = rx.total 𝒰 BinOp

  Magma-path-object : rx.is-univalent Magma
  Magma-path-object =
    total-path-object BinOp U-univ
      (unb-disp-path-object binop-lens
        λ A → prod-path-object (E A × E A) (λ _ → discrete (E A)) (λ _ → disc-path-object _))
```

## Homotopy unordered pairs

After Buchholtz, an unordered pair in a type is a polynomial over the classifying
type of `U`-small types merely equivalent to the booleans. That classifier is a
path object by comprehension — the predicate is a truncation, hence a proposition
— and the decoding lifts discretely, its transport the underlying map of the
equivalence, unital at reflexivity. Partial products give the path object of
unordered pairs valued in any path object.

```agda
  hup-pred : U → Type ℓ'
  hup-pred X = ∥ E X ≃ Bool ∥

  𝔹Σ₂ : reflexive-graph (ℓ ⊔ ℓ') ℓ'
  𝔹Σ₂ = rx.comprehension 𝒰 hup-pred

  E₂ : rx.vfam 𝔹Σ₂ ℓ' ℓ'
  E₂ K = discrete (E (K .fst))

  private
    𝔹Σ₂-univ : rx.is-univalent 𝔹Σ₂
    𝔹Σ₂-univ = compr-path-object 𝒰 hup-pred U-univ (λ _ → squash)

  hUP⁺ : ∀ {w z} → reflexive-graph w z → reflexive-graph (ℓ ⊔ ℓ' ⊔ w) (ℓ' ⊔ z)
  hUP⁺ 𝒜 = cov-poly 𝔹Σ₂ E₂ 𝒜 (λ _ _ f u → f .fst u) (λ _ → refl)

  hUP⁻ : ∀ {w z} → reflexive-graph w z → reflexive-graph (ℓ ⊔ ℓ' ⊔ w) (ℓ' ⊔ z)
  hUP⁻ 𝒜 = ctrv-poly 𝔹Σ₂ E₂ 𝒜 (λ _ _ f u → Equiv.inv f u) (λ _ → refl)

  hUP⁺-path-object : ∀ {w z} (𝒜 : reflexive-graph w z)
                   → rx.is-univalent 𝒜 → rx.is-univalent (hUP⁺ 𝒜)
  hUP⁺-path-object 𝒜 = cov-poly-path-object 𝔹Σ₂ E₂ 𝒜 (λ _ _ f u → f .fst u) (λ _ → refl) 𝔹Σ₂-univ

  hUP⁻-path-object : ∀ {w z} (𝒜 : reflexive-graph w z)
                   → rx.is-univalent 𝒜 → rx.is-univalent (hUP⁻ 𝒜)
  hUP⁻-path-object 𝒜 = ctrv-poly-path-object 𝔹Σ₂ E₂ 𝒜 (λ _ _ f u → Equiv.inv f u) (λ _ → refl) 𝔹Σ₂-univ
```
