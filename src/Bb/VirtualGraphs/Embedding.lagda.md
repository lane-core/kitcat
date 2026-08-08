Representability and the embedding condition over the bare carrier,
and the opposite. Nothing here reads a half-twist: every statement is a
condition on `reflect` alone.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Embedding where

open import Core.Type
open import Core.Base
open import Core.Data.Nat.Type using (Z)
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base using (ap-comp)
open import Core.Transport.J using (J)
open import Core.Transport.Properties
  using (is-prop-is-prop; is-prop→is-set; prop-inhabited→is-contr; snd-contr)
open import Core.HLevel.Base
  using (Π-is-prop; Πi-is-prop; is-prop-equiv; is-prop-×; Π-is-hlevel;
         retract→is-hlevel)
open import Core.Function.Embedding
  using (is-embedding; injective→is-embedding; is-embedding→ap-equiv;
         is-equiv→is-embedding)
open import Core.Equiv.Base using (iso→equiv; is-contr-equiv; _≃_; is-equiv)
open import Core.Equiv.Properties using (esym; Σ-equiv-snd)

open import Bb.VirtualGraphs.Type
```

## Representability

A judgment is representable when it is the reflection of an edge.
Every edge represents its own reflection, and the whole hom type is
equivalent to the total space of represented judgments.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G

  is-representable : ∀ {x y} → judgment x y → Type (o ⊔ h)
  is-representable = fiber reflect

  normal : ∀ {x y} (f : hom x y) → is-representable (reflect f)
  normal f = f , refl

  hom≃total-representable
    : ∀ {x y} → hom x y ≃ (Σ α ∶ judgment x y , is-representable α)
  hom≃total-representable {x} {y} = iso→equiv fwd bwd hom-ret rep-sec
    where
      fwd : hom x y → Σ F ∶ judgment x y , is-representable F
      fwd f = reflect f , (f , refl)

      bwd : (Σ α ∶ judgment x y , is-representable α) → hom x y
      bwd (_ , a , _) = a

      hom-ret : ∀ f → bwd (fwd f) ≡ f
      hom-ret f = refl

      rep-sec : ∀ s → fwd (bwd s) ≡ s
      rep-sec (_ , a , p) = J (λ F' p' → fwd a ≡ (F' , a , p')) refl p
```

## The embedding condition

Representation is unique where it occurs. Propositional fibers is
what an embedding is, so the embedding condition is `reflect` being
one at every pair of objects.

```agda
  reflect-is-embedding : Type (o ⊔ h)
  reflect-is-embedding = ∀ {x y} (α : judgment x y) → is-prop (is-representable α)

  reflect-is-embedding-is-prop : is-prop reflect-is-embedding
  reflect-is-embedding-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _

  reflect-lc : reflect-is-embedding → ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc S {n = n} p = ap fst (S (reflect n) (_ , p) (normal n))

  contr-from-embedding
    : reflect-is-embedding → ∀ {x y} (α : judgment x y)
    → is-representable α → is-contr (is-representable α)
  contr-from-embedding S α = prop-inhabited→is-contr (S α)

  reflect-is-embedding-unfolds : reflect-is-embedding ≡ (∀ {x y} → is-embedding (reflect {x} {y}))
  reflect-is-embedding-unfolds = refl
```

Two representations of one judgment name a path of edges twice
over: cancel `reflect` across the loop that runs through the
judgment, or project the fiber's own path. The two agree, so any
construction stated through the cancellation transports to one
stated in the fiber.

```agda
  reflect-lc-fiber
    : (S : reflect-is-embedding) {x y : ob} (α : judgment x y)
      (u v : is-representable α)
    → reflect-lc S {m = u .fst} {n = v .fst} (u .snd ∙ sym (v .snd))
    ≡ ap fst (S α u v)
  reflect-lc-fiber S α u v =
      ap (ap fst)
        (is-prop→is-set P (φ u) (normal n) (P (φ u) (normal n))
          (P (φ u) (φ v) ∙ P (φ v) (normal n)))
    ∙ ap-comp fst (P (φ u) (φ v)) (P (φ v) (normal n))
    ∙ ap2s _∙_ head tail
    ∙ Path.unitr (ap fst (S α u v))
    where
      n = v .fst

      P : is-prop (is-representable (reflect n))
      P = S (reflect n)

      φ : is-representable α → is-representable (reflect n)
      φ w = w .fst , w .snd ∙ sym (v .snd)

      head : ap fst (P (φ u) (φ v)) ≡ ap fst (S α u v)
      head = ap (ap fst)
        (is-prop→is-set P (φ u) (φ v) (P (φ u) (φ v)) (ap φ (S α u v)))

      tail : ap fst (P (φ v) (normal n)) ≡ refl
      tail = ap (ap fst)
        (is-prop→is-set P (φ v) (normal n) (P (φ v) (normal n))
          (λ i → n , Path.invr (v .snd) i))
```

Where the edges form sets the judgments do too, and an embedding is
then an injection: the embedding condition reduces to injectivity of
`reflect`.

```agda
  embedding-from-injective
    : (∀ {x y} → is-set (hom x y))
    → (∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n)
    → reflect-is-embedding
  embedding-from-injective hset inj α =
    injective→is-embedding (Π-is-hlevel 2 λ _ → hset) reflect inj α
```

## The centred pair

One edge may represent two judgments at once. `centred` is the type of
such an edge together with its two representation witnesses.

```agda
  centred : ∀ {x y} → judgment x y → judgment x y → Type (o ⊔ h)
  centred {x} {y} α β = Σ n ∶ hom x y , (reflect n ≡ α) × (reflect n ≡ β)
```

Composing the second witness with the inverse of the first splits the
pair in two. One factor is the fiber of `reflect` over the first
judgment, the other the path space between the two judgments. The
split reads nothing but `reflect`.

```agda
  centred≃ : ∀ {x y} (α β : judgment x y)
           → centred α β ≃ (is-representable α × (α ≡ β))
  centred≃ α β = iso→equiv fwd bwd sec retr
    where
      fwd : centred α β → is-representable α × (α ≡ β)
      fwd (n , p , q) = (n , p) , sym p ∙ q

      bwd : is-representable α × (α ≡ β) → centred α β
      bwd ((n , p) , s) = n , p , p ∙ s

      sec : (w : centred α β) → bwd (fwd w) ≡ w
      sec (n , p , q) i = n , p , Path.lc (sym p) q i

      retr : (w : is-representable α × (α ≡ β)) → fwd (bwd w) ≡ w
      retr ((n , p) , s) i = (n , p) , Path.lc p s i
```

The embedding condition governs the first factor alone, so it makes
the centred pair a proposition exactly where the path space between
the two judgments is already one. The second factor is a retract of
the pair, so contractibility of the pair carries to that path space.

```agda
  centred-is-prop : reflect-is-embedding → ∀ {x y} {α β : judgment x y}
                  → is-prop (α ≡ β) → is-prop (centred α β)
  centred-is-prop S {α = α} {β = β} pth =
    is-prop-equiv (centred≃ α β) (is-prop-× (S α) pth)

  centred-loop : ∀ {x y} {α β : judgment x y}
               → is-contr (centred α β) → is-contr (α ≡ β)
  centred-loop {α = α} {β = β} c =
    snd-contr (is-contr-equiv (esym (centred≃ α β)) c)
```

Under the embedding condition `ap reflect` has `reflect-lc` as a left
inverse, so a path space of edges is a retract of the path space of
their reflections. Every h-level descends along that retraction.

```agda
  ap-reflect-retr
    : (S : reflect-is-embedding) {x y : ob} {a b : hom x y} (p : a ≡ b)
    → reflect-lc S (ap reflect p) ≡ p
  ap-reflect-retr S {a = a} =
    J (λ _ p' → reflect-lc S (ap reflect p') ≡ p')
      (ap (ap fst)
        (is-prop→is-set (S (reflect a)) (a , refl) (a , refl)
          (S (reflect a) (a , refl) (a , refl)) refl))

  path-lc : (S : reflect-is-embedding) {x y : ob} {a b : hom x y}
          → is-contr (reflect a ≡ reflect b) → is-contr (a ≡ b)
  path-lc S =
    retract→is-hlevel Z (reflect-lc S) (ap reflect) (ap-reflect-retr S)
```

## The opposite

Reversing edges exchanges the two argument halves. The carrier has no
further fields, so doing it twice returns the record on the nose.

```agda
opⱽ : ∀ {o h} → virtual-graph o h → virtual-graph o h
opⱽ G .virtual-graph.ob        = virtual-graph.ob G
opⱽ G .virtual-graph.hom x y   = virtual-graph.hom G y x
opⱽ G .virtual-graph.reflect f γ = virtual-graph.reflect G f (γ .snd , γ .fst)

opⱽ-invol : ∀ {o h} (G : virtual-graph o h) → opⱽ (opⱽ G) ≡ G
opⱽ-invol G = refl
```

The embedding condition crosses the opposite by reindexing a judgment
along the argument exchange, which is an equivalence on fibers.

```agda
op-embedding : ∀ {o h} (G : virtual-graph o h)
             → reflect-is-embedding G → reflect-is-embedding (opⱽ G)
op-embedding G S α =
  is-prop-equiv
    (iso→equiv (λ w → w .fst , λ i δ → w .snd i (δ .snd , δ .fst))
               (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
               (λ _ → refl) (λ _ → refl))
    (S (λ δ → α (δ .snd , δ .fst)))
```

## The swap of arguments

A judgment at the opposite carrier is this carrier's own judgment read
against the exchanged argument. The exchange is its own inverse
definitionally, so the reindexing is an equivalence on judgments, and
`ap` of an equivalence is again one. A fiber of `reflect` over a
judgment is therefore equivalent to a fiber of the opposite `reflect`
over the swapped judgment, and a tier statement transfers along one
`ap` of the swap. Nothing here reads a half-twist.

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G) where

  swap-arg : ∀ {x z} → virtual-graph.argument (opⱽ G) x z → argument z x
  swap-arg γ = γ .snd , γ .fst

  swap-arg⁻ : ∀ {x z} → argument z x → virtual-graph.argument (opⱽ G) x z
  swap-arg⁻ δ = δ .snd , δ .fst

  swap-judgment : ∀ {x z} → judgment z x → virtual-graph.judgment (opⱽ G) x z
  swap-judgment α γ = α (swap-arg γ)

  swap-judgment⁻ : ∀ {x z} → virtual-graph.judgment (opⱽ G) x z → judgment z x
  swap-judgment⁻ β δ = β (swap-arg⁻ δ)

  swap-eqv : ∀ {x z} → judgment z x ≃ virtual-graph.judgment (opⱽ G) x z
  swap-eqv = iso→equiv swap-judgment swap-judgment⁻ (λ _ → refl) (λ _ → refl)

  ap-swap : ∀ {x z} {α β : judgment z x}
          → is-equiv (ap (swap-judgment {x} {z}) {α} {β})
  ap-swap = is-embedding→ap-equiv (is-equiv→is-embedding (swap-eqv .snd))

  rep-op : ∀ {x z} (β : judgment z x)
         → is-representable G β
         ≃ is-representable (opⱽ G) (swap-judgment β)
  rep-op β = Σ-equiv-snd (λ m → ap swap-judgment , ap-swap)
```
