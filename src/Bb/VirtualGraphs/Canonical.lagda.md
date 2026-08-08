Invertibility in one hand, and the unit it yields. An endo-edge is an
equivalence in a hand when both of its translations there are
equivalences of types. One translation cuts it after an edge into its
object, at every source. The other cuts it before an edge out, at
every target. Each half is a family of `is-equiv`, so each is a
proposition.

The telescope is one half-twist family, the embedding condition, and
that hand's cut alone. Neither hand reads the other.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Canonical where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)
open import Core.Transport.J using (subst)
open import Core.Equiv.Base using (_≃_; is-equiv; module Equiv)
open import Core.Equiv.Properties using (is-equiv-is-prop; equiv-lc; equiv-rc)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
```

## Equivalences in the positive hand

An endo-edge at `x` is an equivalence in the positive hand when both
of its translations there are equivalences of types. One translation
cuts it after an edge into `x`, at every source. The other cuts it
before an edge out of `x`, at every target. One equivalence per
object stands in each family. `is-equiv` is a proposition, so both
families are.

Three edges meet at a positive cut, and two of them decide the third.
Where the trailing factor and the whole cut are equivalences in this
hand, so is the leading factor. Each half moves the associator across
a translation and cancels the trailing factor's own translation
against it.

```agda
module invertible⁺ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁺ : framing⁻.is-composable⁺ G rx) where

  open tower⁺ G rx S C⁺ public

  is-eqv⁺ : ∀ {x} → hom x x → Type (o ⊔ h)
  is-eqv⁺ {x} e = ((w : ob) → is-equiv λ (f : hom w x) → f ⨾⁺ e)
                × ((y : ob) → is-equiv λ (g : hom x y) → e ⨾⁺ g)

  eqv-2-out-of-3 : ∀ {x} (f g : hom x x)
                 → is-eqv⁺ g → is-eqv⁺ (f ⨾⁺ g) → is-eqv⁺ f
  eqv-2-out-of-3 {x} f g (gp , gq) (cp , cq) = post , pre
    where
      post : (w : ob) → is-equiv λ (u : hom w x) → u ⨾⁺ f
      post w =
        equiv-lc (λ u → u ⨾⁺ f) (λ u → u ⨾⁺ g) (gp w)
          (subst is-equiv (funext λ u → sym (assoc⁺ u f g)) (cp w))

      pre : (y : ob) → is-equiv λ (u : hom x y) → f ⨾⁺ u
      pre y =
        equiv-rc (λ u → g ⨾⁺ u) (λ u → f ⨾⁺ u) (gq y)
          (subst is-equiv (funext λ u → assoc⁺ f g u) (cq y))
```

Canonicalization at such an edge: `canon` is the edge that the
translation after `e` sends to `e`. It cuts onto `e` without moving
it. It is a right unit of the positive cut at every edge into the
object, and 2-out-of-3 returns it as an equivalence in this hand
again.

The construction is Kraus, *Internal ∞-Categorical Models of
Dependent Type Theory*, §5.2 (`resources/kraus-infty-cwf/notes.tex`
l.869-889), and its companion formalization's `module I`
(`resources/kraus-infty-cwf/Identities.agda:298-339`). `canon` is his
`I`, `canon-cut` his `e⋄I`, `canon-unitr` his `l-ntrl`, and
`canon-is-eqv` the second half of his `I-is-idpt+eqv`.
`eqv-2-out-of-3` is his lemma of that name (`Identities.agda:238-290`)
and `is-eqv⁺` is his `is-eqv` (`Identities.agda:111-113`) read in one
hand. Kraus credits `I` to Capriotti and Kraus (POPL 2018,
`resources/capriotti-kraus-semi-segal`) and to work of Harpaz and
Lurie. He composes applicatively and this library diagrammatically,
so his left neutrality reads here as right neutrality of the positive
cut.

```agda
  module canonical {x : ob} (e : hom x x) (p : is-eqv⁺ e) where
    post : (w : ob) → hom w x ≃ hom w x
    post w = (λ f → f ⨾⁺ e) , p .fst w

    canon : hom x x
    canon = Equiv.inv (post x) e

    canon-cut : canon ⨾⁺ e ≡ e
    canon-cut = Equiv.counit (post x) e

    canon-unitr : ∀ {w} (f : hom w x) → f ⨾⁺ canon ≡ f
    canon-unitr {w} f =
        sym (Equiv.unit (post w) (f ⨾⁺ canon))
      ∙ ap (Equiv.inv (post w)) (assoc⁺ f canon e ∙ ap (f ⨾⁺_) canon-cut)
      ∙ Equiv.unit (post w) f

    canon-is-eqv : is-eqv⁺ canon
    canon-is-eqv =
      eqv-2-out-of-3 canon e p (subst (is-eqv⁺ {x}) (sym canon-cut) p)
```

## Equivalences in the negative hand

The mirror reads both translations through the negative cut.

```agda
module invertible⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower⁻ G corx S C⁻ public

  is-eqv⁻ : ∀ {x} → hom x x → Type (o ⊔ h)
  is-eqv⁻ {x} e = ((w : ob) → is-equiv λ (f : hom w x) → f ⨾⁻ e)
                × ((y : ob) → is-equiv λ (g : hom x y) → e ⨾⁻ g)
```
