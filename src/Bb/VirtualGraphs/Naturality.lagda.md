Naturality of a half-twist carried across the tower. `Framing` states
the two tiers over the framing alone. Each tier's centre represents
both flanks of its hand, so under the embedding condition it delivers
the hand's naturality equation, and the judgment form and the
contractible form carry each other.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Naturality where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module Path)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Transport.Properties
  using (is-contr-is-prop; is-contr-×; prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; module diagonal)
open import Core.Equiv.Base using (is-contr-equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
```

## The transfer

```agda
module transfer {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower G rx corx S C⁺ C⁻ public
  open framing G rx corx
    using (own⁻; own⁺; is-natural⁻; is-natural⁺; is-naturalᴶ⁻; is-naturalᴶ⁺)
```

## Naturality over the tower

A tier's centre represents both flanks. The embedding condition
identifies it with each cut's own representative, and the two
identifications concatenate into the square. Each hand reads its own
tier alone.

```agda
  nat⁻ : is-natural⁻ → nat⁻-law
  nat⁻ N {x} {y} m = sym u ∙ v
    where
      c : own⁻ m
      c = N m .center

      u : c .fst ≡ rx x ⨾⁻ m
      u = ap fst (S (composite⁻ (rx x) m)
            (c .fst , c .snd .fst)
            (rx x ⨾⁻ m , reflect-⨾⁻ (rx x) m))

      v : c .fst ≡ m ⨾⁻ rx y
      v = ap fst (S (composite⁻ m (rx y))
            (c .fst , c .snd .snd)
            (m ⨾⁻ rx y , reflect-⨾⁻ m (rx y)))

  nat⁺ : is-natural⁺ → nat⁺-law
  nat⁺ N {x} {y} m = sym u ∙ v
    where
      c : own⁺ m
      c = N m .center

      u : c .fst ≡ corx x ⨾⁺ m
      u = ap fst (S (composite⁺ (corx x) m)
            (c .fst , c .snd .fst)
            (corx x ⨾⁺ m , reflect-⨾⁺ (corx x) m))

      v : c .fst ≡ m ⨾⁺ corx y
      v = ap fst (S (composite⁺ m (corx y))
            (c .fst , c .snd .snd)
            (m ⨾⁺ corx y , reflect-⨾⁺ m (corx y)))
```

Each cut's witness identifies its judgment with the reflection of the
representative, so a tier's path space between judgments is the path
space between two edges. The diagonal collapses that path space onto
a loop space, at the flank each hand's framing supplies.

```agda
  flank⁻ : is-natural⁻ → ∀ {x y} (m : hom x y)
         → is-contr (rx x ⨾⁻ m ≡ m ⨾⁻ rx y)
  flank⁻ N {x} {y} m =
    path-lc G S
      (subst (λ β → is-contr (reflect (rx x ⨾⁻ m) ≡ β))
             (sym (reflect-⨾⁻ m (rx y)))
        (subst (λ α → is-contr (α ≡ composite⁻ m (rx y)))
               (sym (reflect-⨾⁻ (rx x) m))
          (centred-loop G (N m))))

  flank⁺ : is-natural⁺ → ∀ {x y} (m : hom x y)
         → is-contr (corx x ⨾⁺ m ≡ m ⨾⁺ corx y)
  flank⁺ N {x} {y} m =
    path-lc G S
      (subst (λ β → is-contr (reflect (corx x ⨾⁺ m) ≡ β))
             (sym (reflect-⨾⁺ m (corx y)))
        (subst (λ α → is-contr (α ≡ composite⁺ m (corx y)))
               (sym (reflect-⨾⁺ (corx x) m))
          (centred-loop G (N m))))

  loop⁻ : is-natural⁻ → ∀ {x y} (m : hom x y)
        → is-contr (flanks.P m ≡ flanks.P m)
  loop⁻ N m = diagonal.loopl (flank⁻ N m)

  loop⁺ : is-natural⁺ → ∀ {x y} (m : hom x y)
        → is-contr (flanks.Q m ≡ flanks.Q m)
  loop⁺ N m = diagonal.loopr (flank⁺ N m)
```

The judgment equation inhabits the tier's second factor. Going back
needs one more datum: the loop space of the leading judgment is a
proposition. Under the embedding condition and the hand's own cut, the
two readings differ by that demand alone.

```agda
  toᴶ⁻ : is-natural⁻ → is-naturalᴶ⁻
  toᴶ⁻ N m = sym (N m .center .snd .fst) ∙ N m .center .snd .snd

  toᴶ⁺ : is-natural⁺ → is-naturalᴶ⁺
  toᴶ⁺ N m = sym (N m .center .snd .fst) ∙ N m .center .snd .snd

  centreᴶ⁻ : is-naturalᴶ⁻ → ∀ {x y} (m : hom x y) → own⁻ m
  centreᴶ⁻ q {x} m = rx x ⨾⁻ m
                   , reflect-⨾⁻ (rx x) m
                   , reflect-⨾⁻ (rx x) m ∙ q m

  centreᴶ⁺ : is-naturalᴶ⁺ → ∀ {x y} (m : hom x y) → own⁺ m
  centreᴶ⁺ q {x} m = corx x ⨾⁺ m
                   , reflect-⨾⁺ (corx x) m
                   , reflect-⨾⁺ (corx x) m ∙ q m

  tierᴶ⁻ : is-naturalᴶ⁻
         → (∀ {x y} (m : hom x y)
            → is-prop (composite⁻ (rx x) m ≡ composite⁻ (rx x) m))
         → is-natural⁻
  tierᴶ⁻ q L {x} m =
    is-contr-equiv (centred≃ G _ _)
      (is-contr-× (contr-from-embedding G S _ (C⁻ (rx x) m))
                  (prop-inhabited→is-contr (diagonal.fold (q m) (L m)) (q m)))

  tierᴶ⁺ : is-naturalᴶ⁺
         → (∀ {x y} (m : hom x y)
            → is-prop (composite⁺ (corx x) m ≡ composite⁺ (corx x) m))
         → is-natural⁺
  tierᴶ⁺ q L {x} m =
    is-contr-equiv (centred≃ G _ _)
      (is-contr-× (contr-from-embedding G S _ (C⁺ (corx x) m))
                  (prop-inhabited→is-contr (diagonal.fold (q m) (L m)) (q m)))
```

The square follows from the equation alone. The equation makes the two
flanks represent one judgment, the embedding condition identifies
their representatives, and `ap fst` reads that on edges. Reflection
carries the square back, since each cut's witness identifies its
judgment with the reflected representative.

```agda
  fromᴶ⁻ : is-naturalᴶ⁻ → nat⁻-law
  fromᴶ⁻ q {x} {y} m =
    ap fst (S (composite⁻ (rx x) m)
              (rx x ⨾⁻ m , reflect-⨾⁻ (rx x) m)
              (m ⨾⁻ rx y , reflect-⨾⁻ m (rx y) ∙ sym (q m)))

  fromᴶ⁺ : is-naturalᴶ⁺ → nat⁺-law
  fromᴶ⁺ q {x} {y} m =
    ap fst (S (composite⁺ (corx x) m)
              (corx x ⨾⁺ m , reflect-⨾⁺ (corx x) m)
              (m ⨾⁺ corx y , reflect-⨾⁺ m (corx y) ∙ sym (q m)))

  judg⁻ : nat⁻-law → is-naturalᴶ⁻
  judg⁻ N {x} {y} m =
      sym (reflect-⨾⁻ (rx x) m)
    ∙ ap reflect (N m)
    ∙ reflect-⨾⁻ m (rx y)

  judg⁺ : nat⁺-law → is-naturalᴶ⁺
  judg⁺ N {x} {y} m =
      sym (reflect-⨾⁺ (corx x) m)
    ∙ ap reflect (N m)
    ∙ reflect-⨾⁺ m (corx y)
```
