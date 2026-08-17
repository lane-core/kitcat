A virtual 2-graph has directed 2-cells between parallel edges and a
chosen composite for each composable pair.  The composite condition says
that the total space of edges receiving a 2-cell from that chosen
composite is contractible, with `ceqv` providing its canonical point.

The contraction first produces a based identity system over each
composite.  Thus a 2-cell out of a composite is equivalent to a path out
of it.  Right units then make every edge a composite, extending this
local result to every 2-cell type.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.2CellEqvId where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Equiv.Base using (_≃_)
open import Core.Equiv.Properties using (_∙e_)
open import Core.IdSys
  using ( is-based-identity-system; Ids-based→equiv⁻
        ; to-path; to-path-over )
open import Core.Kan using (is-contr→is-prop)
open import Core.Transport.Base using (transport)
open import Core.Transport.Properties using (transport-equiv)

record virtual o h c : Type₊ (o ⊔ h ⊔ c) where
  no-eta-equality
  infix 6 _⇒_
  infixr 9 _⨾_
  field
    ob : Type o
    hom : ob → ob → Type h
    _⇒_ : ∀ {x y} → hom x y → hom x y → Type c
    _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z

    ceqv
      : ∀ {x y z} {f : hom x y} {g : hom y z}
      → (f ⨾ g) ⇒ (f ⨾ g)

    cut-unique
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-prop (Σ s ∶ hom x z , (f ⨾ g) ⇒ s)

module _ {o h c} (V : virtual o h c) where
  private
    module V = virtual V
  open V

  cut-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (Σ s ∶ hom x z , (f ⨾ g) ⇒ s)
  cut-contr f g .center = f ⨾ g , ceqv
  cut-contr f g .paths = cut-unique f g (f ⨾ g , ceqv)

  cut-path
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → (p : Σ s ∶ hom x z , (f ⨾ g) ⇒ s)
    → (f ⨾ g , ceqv) ≡ p
  cut-path {f = f} {g} p =
    is-contr→is-prop (cut-contr f g) (f ⨾ g , ceqv) p

  cast-path
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → (f ⨾ g) ⇒ s
    → f ⨾ g ≡ s
  cast-path α = ap fst (cut-path (_ , α))

  cast-pathp
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → (α : (f ⨾ g) ⇒ s)
    → PathP (λ i → (f ⨾ g) ⇒ cast-path α i) ceqv α
  cast-pathp α = ap snd (cut-path (_ , α))

  based-ids
    : ∀ {x y z} {f : hom x y} {g : hom y z}
    → is-based-identity-system (f ⨾ g) ((f ⨾ g) ⇒_) ceqv
  based-ids .to-path = cast-path
  based-ids .to-path-over = cast-pathp

  composite-cell≃path
    : ∀ {x y z} (f : hom x y) (g : hom y z) (s : hom x z)
    → ((f ⨾ g) ⇒ s) ≃ (f ⨾ g ≡ s)
  composite-cell≃path f g s = Ids-based→equiv⁻ based-ids

record right-unital {o h c} (V : virtual o h c) : Type (o ⊔ h) where
  no-eta-equality
  private
    module V = virtual V
  open V
  field
    idn : (x : ob) → hom x x
    unitr : ∀ {x y} (f : hom x y) → f ⨾ idn y ≡ f

module _ {o h c} (V : virtual o h c) (U : right-unital V) where
  private
    module V = virtual V
    module U = right-unital U
  open V
  open U

  reindex : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B
  reindex p = transport p , transport-equiv p

  cell≃path
    : ∀ {x y} (f s : hom x y)
    → (f ⇒ s) ≃ (f ≡ s)
  cell≃path {y = y} f s =
      reindex (ap (λ h → h ⇒ s) (sym u))
    ∙e composite-cell≃path V f (idn y) s
    ∙e reindex (ap (_≡ s) u)
    where
      u : f ⨾ idn y ≡ f
      u = unitr f
```
