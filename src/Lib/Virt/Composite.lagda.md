Lane Biocini

```
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Virt.Composite where

open import Lib.Core.Prim
open import Lib.Core.Base
open import Lib.Core.Type
open import Lib.Core.HLevel
open import Lib.Core.Cast
open import Lib.Virt.Base

module _ {u} {Γ : Type u} ⦃ V : Virtual Γ ⦄ where
  open Virtual V

  module _ (C : Γ) where
    private
      infix 6 _~>_ _=>_
      _~>_ = hom C
      _=>_ = hom2 C
      _⨾_ = cut
      _⊚_ = vcut; infixr 9 _⨾_ _⊚_
      _●_ = hcut; infixr 8 _●_

    cidem : ∀ {a b c} {f : a ~> b} {g : b ~> c} → ceqv ⊚ ceqv ≡ ceqv {f = f} {g}
    cidem {f = f} {g} = ap fst total where
      is-lin : ceqv ⊚ (ceqv ⊚ ceqv) ≡ ceqv ⊚ ceqv
      is-lin = c-wlinear ceqv

      total : (ceqv ⊚ ceqv , is-lin) ≡ (ceqv , refl)
      total = is-contr→is-prop (ceqv-divl (ceqv ⊚ ceqv)) _ _

    vcut-unitl : ∀ {a b c} {f : a ~> b} {g : b ~> c} {k : a ~> c}
               → (α : f ⨾ g => k) → ceqv ⊚ α ≡ α
    vcut-unitl {f = f} {g} α = ap fst total where
      total : (ceqv ⊚ α , c-wlinear α) ≡ (α , refl)
      total = is-contr→is-prop (ceqv-divl (ceqv ⊚ α)) _ _

    vcut-unitr : ∀ {a b c} {h : a ~> c} {f : a ~> b} {g : b ~> c}
               → (α : h => f ⨾ g) → α ⊚ ceqv ≡ α
    vcut-unitr {f = f} {g} α = ap fst total where
      total : (α ⊚ ceqv , c-wthunkable α) ≡ (α , refl)
      total = is-contr→is-prop (ceqv-divr (α ⊚ ceqv)) _ _

    based-ids : ∀ {x y z} {f : x ~> y} {g : y ~> z}
              → is-based-identity-system (f ⨾ g) (f ⨾ g =>_) ceqv
    based-ids .to-path = cast-path
    based-ids .to-path-over = cast-pathp

    cobased-ids : ∀ {x y z} {f : x ~> y} {g : y ~> z}
                → is-based-identity-system (f ⨾ g) (_=> (f ⨾ g)) ceqv
    cobased-ids .to-path α = ap fst (cocut-unique C (_ , ceqv) (_ , α))
    cobased-ids .to-path-over α = ap snd (cocut-unique C (_ , ceqv) (_ , α))

    cut-contr : ∀ {a b c} {f : a ~> b} {g : b ~> c}
              → is-contr (Σ s ∶ a ~> c , (f ⨾ g) => s)
    cut-contr {f = f} {g} = prop-inhabited→is-contr (cut-unique C) (f ⨾ g , ceqv)

    cocut-contr : ∀ {a b c} {f : a ~> b} {g : b ~> c}
                → is-contr (Σ t ∶ a ~> c , t => (f ⨾ g))
    cocut-contr {f = f} {g} = prop-inhabited→is-contr (cocut-unique C) (f ⨾ g , ceqv)

```

core groupoid structure lifts onto 2-cells over composites

```

    loop : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
         → f ⨾ g => s → s => s
    loop {s} p = transport (λ i → hom2 C (cast-path p i) s) p

    lift-path : ∀ {x y z} {f : x ~> y} {g : y ~> z} {r s : x ~> z}
              → f ⨾ g => r → r ≡ s → r => s
    lift-path {r} {s} α q = transport (λ i → hom2 C r (q i)) (loop α)

    csym : ∀ {x y z} {f : x ~> y} {g : y ~> z} {s : x ~> z}
         → f ⨾ g => s → s => f ⨾ g
    csym {s} α = transport (λ i → hom2 C s (cast-path α (~ i))) (loop α)

    cconcat : ∀ {w x y z} {f : w ~> x} {f' : x ~> z} {g : w ~> y} {g' : y ~> z} {s : w ~> z}
            → f ⨾ f' => g ⨾ g' → g ⨾ g' => s → f ⨾ f' => s
    cconcat {f} {f'} α β = transport (λ i → hom2 C (cut f f') (cast-path β i)) α

    module _ {w x y z} {f : w ~> x} {g : x ~> y} {h : y ~> z} where
      lwhisk : {s : w ~> y} → f ⨾ g => s → (f ⨾ g) ⨾ h => s ⨾ h
      lwhisk H = transport (λ i → (f ⨾ g) ⨾ h => cast-path H i ⨾ h) ceqv

      lwhisk-op : {s : w ~> y} → f ⨾ g => s → s ⨾ h => (f ⨾ g) ⨾ h
      lwhisk-op H = transport (λ i → cast-path H i ⨾ h => (f ⨾ g) ⨾ h) ceqv

      rwhisk : {r : x ~> z} → g ⨾ h => r → f ⨾ (g ⨾ h) => f ⨾ r
      rwhisk K = transport (λ i → f ⨾ (g ⨾ h) => f ⨾ cast-path K i) ceqv

      rwhisk-op : {r : x ~> z} → g ⨾ h => r → f ⨾ r => f ⨾ (g ⨾ h)
      rwhisk-op K = transport (λ i → f ⨾ cast-path K i => f ⨾ (g ⨾ h)) ceqv

      conj : {s : w ~> y} {r : x ~> z}
           → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h) → f ⨾ g => s → g ⨾ h => r → s ⨾ h => f ⨾ r
      conj A H K = transport (λ i → cast-path H i ⨾ h => f ⨾ cast-path K i) A

      lcross : {s : w ~> y} → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h) → f ⨾ g => s → s ⨾ h => f ⨾ (g ⨾ h)
      lcross A H = transport (λ i → cast-path H i ⨾ h => f ⨾ (g ⨾ h)) A

      rcross : {r : x ~> z} → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h) → g ⨾ h => r → (f ⨾ g) ⨾ h => f ⨾ r
      rcross A K = transport (λ i → (f ⨾ g) ⨾ h => (f ⨾ cast-path K i)) A
