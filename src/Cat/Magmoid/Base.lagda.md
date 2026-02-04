Lane Biocini
February 2025

Virtual graph composite systems and their derived operations.

The composite module expresses the universal property of a composition
operation: composites are unique up to a 2-cell witness, and this
uniqueness yields a based identity system. From this, we derive
cast-path (converting 2-cells to paths), whiskering operations,
cancellation lemmas, inverse extraction, and naturality squares.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Magmoid.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan hiding (assoc; eqvl; eqvr)
open import Core.Transport
open import Core.Equiv

module composite {o h h'} {O : Type o}
  (H : O → O → Type h)
  (H2 : ∀ {a b} → H a b → H a b → Type h')
  (cat : ∀ {a b c} → H a b → H b c → H a c)
  (univ : ∀ {a b c} (f : H a b) (g : H b c)
        → is-prop (Σ s ∶ H a c , H2 (cat f g) s))
  (comp : ∀ {a b c} {f : H a b} {g : H b c}
        → H2 (cat f g) (cat f g))
  where
  private
    ob = O
    hom = H
    _⨾_ = cat; infixr 40 _⨾_
    _=>_ = H2; infix 4 _=>_

  module base where
    fibroid : ∀ {x y z} → hom y z → hom x z → Type (h ⊔ h')
    fibroid {x} {y} g s = Σ f ∶ hom x y , f ⨾ g => s

    cofibroid : ∀ {x y z} → hom x y → hom x z → Type (h ⊔ h')
    cofibroid {y} {z} f s = Σ g ∶ hom y z , f ⨾ g => s

    module _ {x y} (f : hom x y) where
      is-left-divisible : Type (o ⊔ h ⊔ h')
      is-left-divisible = ∀ {w} (s : hom w y) → is-contr (fibroid f s)

      is-right-divisible : Type (o ⊔ h ⊔ h')
      is-right-divisible = ∀ {z} (s : hom x z) → is-contr (cofibroid f s)

    is-eqv : ∀ {x y} → hom x y → Type (o ⊔ h ⊔ h')
    is-eqv {x} {y} f =
      is-left-divisible f × is-right-divisible f

    _≅_ : ob → ob → Type (o ⊔ h ⊔ h')
    x ≅ y = Σ f ∶ hom x y , is-eqv f

    commutative-sq
      : ∀ {a b c d}
      → (f : hom a b) (g : hom a c)
        (h : hom b d) (k : hom c d)
      → Type _
    commutative-sq f g h k = g ⨾ k ≡ f ⨾ h

  module units where
    module _ {x} (e : hom x x) where
      lunital runital : Type (o ⊔ h)
      lunital = ∀ {y} (f : hom x y)
        → e ⨾ (e ⨾ f) ≡ e ⨾ f
      runital = ∀ {w} (f : hom w x)
        → (f ⨾ e) ⨾ e ≡ f ⨾ e

      record is-unital : Type (o ⊔ h ⊔ h') where
        field
          eqv : base.is-eqv e
          lcoh : lunital
          rcoh : runital

  unital : ∀ x → Type (o ⊔ h ⊔ h')
  unital x = Σ i ∶ hom x x , units.is-unital i

  module ids where
    cast-path
      : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
      → f ⨾ g => s → f ⨾ g ≡ s
    cast-path {f = f} {g} α =
      ap fst (univ f g (f ⨾ g , comp) (_ , α))

    cast-pathp
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {s : hom x z}
      → (α : f ⨾ g => s)
      → PathP (λ i → f ⨾ g => cast-path α i) comp α
    cast-pathp {f = f} {g} α =
      ap snd (univ f g (f ⨾ g , comp) (_ , α))

    cut-contr
      : ∀ {x y z} {f : hom x y} {g : hom y z}
      → is-contr (Σ s ∶ hom x z , f ⨾ g => s)
    cut-contr {f = f} {g} =
      prop-inhabited→is-contr (univ f g) (f ⨾ g , comp)

    based-ids
      : ∀ {x y z} {f : hom x y} {g : hom y z}
      → is-based-identity-system (f ⨾ g) (f ⨾ g =>_) comp
    based-ids .to-path = cast-path
    based-ids .to-path-over = cast-pathp

    loop
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {s : hom x z}
      → f ⨾ g => s → s => s
    loop {s = s} α =
      transport (λ i → cast-path α i => s) α

    lift-path
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {r s : hom x z}
      → f ⨾ g => r → r ≡ s → r => s
    lift-path {r = r} α q =
      transport (λ i → r => q i) (loop α)

    comp-unique
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {s s' : hom x z}
      → f ⨾ g => s → f ⨾ g => s' → s ≡ s'
    comp-unique α β =
      sym (cast-path α) ∙ cast-path β

    vsym
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {s : hom x z}
      → f ⨾ g => s → s => f ⨾ g
    vsym {s = s} α =
      transport (λ i → s => cast-path α (~ i)) (loop α)

    vcat
      : ∀ {x y z} {f : hom x y} {g : hom y z}
        {s s' : hom x z}
      → f ⨾ g => s → s => s' → f ⨾ g => s'
    vcat {s' = s'} α β =
      transport (λ i → cast-path α (~ i) => s') β


  module properties where
    open base
    divr→lcancel
      : ∀ {x y z} {f : hom x y} {k₁ k₂ : hom y z}
      → (∀ s → is-contr (cofibroid f s))
      → f ⨾ k₁ => f ⨾ k₂ → k₁ ≡ k₂
    divr→lcancel {f = f} {k₁} {k₂} f-div σ =
      ap fst (is-contr→is-prop (f-div (f ⨾ k₂))
        (k₁ , σ) (k₂ , comp))

    divl→rcancel
      : ∀ {w x y} {g : hom x y} {h₁ h₂ : hom w x}
      → (∀ s → is-contr (fibroid g s))
      → h₁ ⨾ g => h₂ ⨾ g → h₁ ≡ h₂
    divl→rcancel {g = g} {h₁} {h₂} g-div σ =
      ap fst (is-contr→is-prop (g-div (h₂ ⨾ g))
        (h₁ , σ) (h₂ , comp))

    is-eqv-is-prop
      : ∀ {x y} (f : hom x y) → is-prop (is-eqv f)
    is-eqv-is-prop f = is-prop-×
      (Πi-is-prop λ _ → Π-is-prop λ _ →
        is-contr-is-prop _)
      (Πi-is-prop λ _ → Π-is-prop λ _ →
        is-contr-is-prop _)

    module iso {x y} {f : hom x y}
      (e : is-eqv f) where

      linv : ∀ {z} → hom x z → hom y z
      linv g = e .snd g .center .fst

      rinv : ∀ {w} → hom w y → hom w x
      rinv g = e .fst g .center .fst

      lunit : hom y y
      lunit = linv f

      runit : hom x x
      runit = rinv f

      pre-counit : ∀ {z} (g : hom x z)
        → f ⨾ linv g => g
      pre-counit g = e .snd g .center .snd

      post-counit : ∀ {w} (g : hom w y)
        → rinv g ⨾ f => g
      post-counit g =
        e .fst g .center .snd

      pre-unit-path : ∀ {z} (g : hom y z)
        → linv (f ⨾ g) ≡ g
      pre-unit-path g =
        ap fst (e .snd (f ⨾ g) .paths (g , comp))

      post-unit-path : ∀ {w} (g : hom w x)
        → rinv (g ⨾ f) ≡ g
      post-unit-path g =
        ap fst (e .fst (g ⨾ f) .paths (g , comp))

  module hgroupoid where
    infixr 25 _▹_
    _▹_
      : ∀ {x y z} {f f' : hom x y}
      → f ≡ f' → (h : hom y z)
      → (f ⨾ h) ≡ (f' ⨾ h)
    γ ▹ h = ap (_⨾ h) γ

    infixl 26 _◃_
    _◃_
      : ∀ {w x y} (h : hom w x)
      → {f f' : hom x y} → f ≡ f'
      → (h ⨾ f) ≡ (h ⨾ f')
    h ◃ γ = ap (h ⨾_) γ

    nat-sq
      : ∀ {x y z} {f f' : hom x y}
        {g g' : hom y z}
      → (α : f ≡ f') (β : g ≡ g')
      → Square (α ▹ g) (f ◃ β) (α ▹ g') (f' ◃ β)
    nat-sq α β i j = α j ⨾ β i

  module coherence
    (units : ∀ x →  Σ i ∶ hom x x , units.is-unital i)
    (α : ∀ {a b c d} (f : hom a b) (g : hom b c) (h : hom c d)
       → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h))
    where
    assoc-path : ∀ {a b c d} (f : hom a b) (g : hom b c) (h : hom c d)
               → f ⨾ (g ⨾ h) ≡ (f ⨾ g) ⨾ h
    assoc-path f g h = sym (ids.cast-path (α f g h))

```
Not needed yet, so commented out

    -- module whiskering
    --   {w x y z} {f : hom w x}
    --   {g : hom x y} {h : hom y z}
    --   where
    --   lwhisk
    --     : {s : hom w y}
    --     → f ⨾ g => s → (f ⨾ g) ⨾ h => s ⨾ h
    --   lwhisk α =
    --     transport
    --       (λ i → (f ⨾ g) ⨾ h => cast-path α i ⨾ h)
    --       comp

    --   lwhisk-op
    --     : {s : hom w y}
    --     → f ⨾ g => s → s ⨾ h => (f ⨾ g) ⨾ h
    --   lwhisk-op α =
    --     transport
    --       (λ i → cast-path α i ⨾ h => (f ⨾ g) ⨾ h)
    --       comp

    --   rwhisk
    --     : {r : hom x z}
    --     → g ⨾ h => r → f ⨾ (g ⨾ h) => f ⨾ r
    --   rwhisk α =
    --     transport
    --       (λ i → f ⨾ (g ⨾ h) => f ⨾ cast-path α i)
    --       comp

    --   rwhisk-op
    --     : {r : hom x z}
    --     → g ⨾ h => r → f ⨾ r => f ⨾ (g ⨾ h)
    --   rwhisk-op α =
    --     transport
    --       (λ i → f ⨾ cast-path α i => f ⨾ (g ⨾ h))
    --       comp

    --   conj
    --     : {s : hom w y} {r : hom x z}
    --     → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h)
    --     → f ⨾ g => s → g ⨾ h => r
    --     → s ⨾ h => f ⨾ r
    --   conj A α β = transport
    --     (λ i → cast-path α i ⨾ h
    --          => f ⨾ cast-path β i)
    --     A

    --   lcross
    --     : {s : hom w y}
    --     → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h)
    --     → f ⨾ g => s
    --     → s ⨾ h => f ⨾ (g ⨾ h)
    --   lcross A α = transport
    --     (λ i → cast-path α i ⨾ h
    --          => f ⨾ (g ⨾ h))
    --     A

    --   rcross
    --     : {r : hom x z}
    --     → (f ⨾ g) ⨾ h => f ⨾ (g ⨾ h)
    --     → g ⨾ h => r
    --     → (f ⨾ g) ⨾ h => f ⨾ r
    --   rcross A β = transport
    --     (λ i → (f ⨾ g) ⨾ h
    --          => f ⨾ cast-path β i)
    --     A

```

record has-virtual-graph {u} o h h' (X : Type u)
  : Type (o ₊ ⊔ h ₊ ⊔ h' ₊ ⊔ u) where
  no-eta-equality
  field
    ob : X → Type o
    hom : ∀ x → ob x → ob x → Type h
    hom2 : ∀ x {a b} → hom x a b → hom x a b → Type h'
    cut : ∀ x {a b c} → hom x a b → hom x b c → hom x a c
    univ
      : ∀ x {a b c} (f : hom x a b) (g : hom x b c)
      → is-prop (Σ s ∶ hom x a c , hom2 x (cut x f g) s)
    comp
      : ∀ x {a b c} {f : hom x a b} {g : hom x b c}
      → hom2 x (cut x f g) (cut x f g)

virtual-graph : ∀ u o h h' → Type₊ (u ⊔ o ⊔ h ⊔ h')
virtual-graph u o h h' = Σ X ∶ Type u , has-virtual-graph o h h' X

```

## Virtual structure

```agda
private
  module H {u o h h'} ((X , M) : virtual-graph u o h h') (C : X) where
    private module M = has-virtual-graph M
    ob = M.ob C
    hom = M.hom C
    hom2 = M.hom2 C
    _⨾_ = M.cut C; infixr 40 _⨾_
    univ = M.univ C
    comp = M.comp C

    open composite.base hom hom2 _⨾_ univ comp public

  module U {u u' o o' h h' k k'}
    ((X , M) : virtual-graph u o h k)
    ((Y , N) : virtual-graph u' o' h' k')
    where
    module _ (C : X) (D : Y) where
      private module C = H (X , M) C
      private module D = H (Y , N) D

      record functor : Type (u ⊔ u' ⊔ o ⊔ o' ⊔ h ⊔ h' ⊔ k ⊔ k') where
        no-eta-equality
        field
          map  : C.ob → D.ob
          hmap : ∀ {x y}
            → C.hom x y → D.hom (map x) (map y)
          preserves-iso : ∀ {x y} (f : C.hom x y)
            → C.is-eqv f → D.is-eqv (hmap f)
          preserves-comp : ∀ {x y z}
            (f : C.hom x y) (g : C.hom y z)
            → D.hom2 (D._⨾_ (hmap f) (hmap g)) (hmap (C._⨾_ f g))

      {-# INLINE functor.constructor #-}

    module _ {C : X} {D : Y} (F G : functor C D) where
      private
        module C = H (X , M) C
        module D = H (Y , N) D
        module F = functor F
        module G = functor G

      record nat-trans : Type (o ⊔ h ⊔ k ⊔ o' ⊔ h' ⊔ k') where
        no-eta-equality
        field
          component : ∀ x
            → D.hom (F.map x) (G.map x)
          natural : ∀ {x y} (f : C.hom x y)
            → D.hom2 (D._⨾_ (F.hmap f) (component y)) (D._⨾_ (component x) (G.hmap f))

      {-# INLINE nat-trans.constructor #-}

    module _ {C : X} {D : Y} where
      private
        module C = H (X , M) C
        module D = H (Y , N) D
      is-nat-iso : {F G : functor C D} → nat-trans F G → Type (o ⊔ o' ⊔ h' ⊔ k')
      is-nat-iso alpha = ∀ x → D.is-eqv (nat-trans.component alpha x)

      nat-iso : (F G : functor C D) → Type _
      nat-iso F G = Σ alpha ∶ nat-trans F G , is-nat-iso alpha

      _⇒_ : functor C D → functor C D → Type _
      _⇒_ = nat-trans

module het {u u' o o' h h' k k'}
  ((X , M) : virtual-graph u o h k)
  ((Y , N) : virtual-graph u' o' h' k')
  where
  module map = U (X , M) (Y , N)
  private module map-op = U (Y , N) (X , M)

  record adjunction {C : X} {D : Y}
    (F : map.functor C D) (G : map-op.functor D C)
    : Type (u ⊔ u' ⊔ o ⊔ o' ⊔ h ⊔ h' ⊔ k ⊔ k')
    where
    no-eta-equality
    private
      module C = H (X , M) C
      module D = H (Y , N) D
      module F = map.functor F
      module G = map-op.functor G

    field
      hom-equiv : ∀ x y → D.hom (F.map x) y ≃ C.hom x (G.map y)

    adjunct : ∀ {x y} → D.hom (F.map x) y → C.hom x (G.map y)
    adjunct {x} {y} = Equiv.fwd (hom-equiv x y)

    coadjunct : ∀ {x y} → C.hom x (G.map y) → D.hom (F.map x) y
    coadjunct {x} {y} = Equiv.inv (hom-equiv x y)

    field
      natural-dom
        : ∀ {x x' y} (f : C.hom x' x) (g : D.hom (F.map x) y)
        → C.hom2 (adjunct (D._⨾_ (F.hmap f) g)) (C._⨾_ f (adjunct g))
      natural-cod
        : ∀ {x y y'} (g : D.hom (F.map x) y) (k : D.hom y y')
        → C.hom2 (adjunct (D._⨾_ g k)) (C._⨾_ (adjunct g) (G.hmap k))

  {-# INLINE adjunction.constructor #-}
  _⊣_ = adjunction

  module _ {C : X} {D : Y} where
    is-left-adjoint : map.functor C D → Type _
    is-left-adjoint F = Σ G ∶ map-op.functor D C , adjunction F G

    is-right-adjoint : map-op.functor D C → Type _
    is-right-adjoint G = Σ F ∶ map.functor C D , adjunction F G

module 2-magmoid {adj₁ adj₂ : Level → Level}
  (X : ∀ o h → virtual-graph (adj₁ (o ⊔ h)) o h (adj₂ h))
  where
  module morphism {o h} (C : X o h .fst) = H (X o h) C

  private module Ht {o o' h h'} = het (X o h) (X o' h')
  open Ht hiding (module map) public

  open Ht.map public

```
