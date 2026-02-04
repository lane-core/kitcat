Lane Biocini
February 2025

Wild categories with quasi-unital identities.

In what follows we engages in a synthesis over the following
constructions, but guided along the lines of Chen's "2-Coherent
Internal Models of Homotopical Type Theory" as well as
Capirotti-Kraus' work. The idea is we define a notion of identity that
is a *characterization* of the sort of data that satisfies the
definition of a unital morphism, such that any other morphism
satisfying this characterization is provably identical to the
canonical one.

Implicitly this entails we shift our perspective with regard to
functors, natural transformations, and so on, where we eschew
laws applying to specific units and instead just ensure each
categorical construction respects isomorphisms.

References:
- John Chen, "Semicategories with Identities"
           & "2-Coherent Internal Models of Homotopical Type Theory"
- Capriotti-Kraus, "Univalent Higher Categories via Complete Semi-Segal Types"

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.HLevel
open import Core.Kan hiding (assoc; eqvl; eqvr)
open import Core.Transport
open import Core.Equiv

record precategory u v : Type₊ (u ⊔ v) where
  no-eta-equality
  infixr 40 _⨾_
  field
    ob  : Type u
    hom : ob → ob → Type v
    _⨾_ : ∀ {a b c} → hom a b → hom b c → hom a c

  is-eqv : ∀ {x y} → hom x y → Type (u ⊔ v)
  is-eqv {x} {y} f = (∀ {z} → is-equiv (λ (g : hom y z) → f ⨾ g))
                   × (∀ {w} → is-equiv (λ (g : hom w x) → g ⨾ f))

  iso : ob → ob → Type (u ⊔ v)
  iso x y = Σ f ∶ hom x y , is-eqv f

  is-unital : ob → Type (u ⊔ v)
  is-unital x = Σ i ∶ hom x x , is-eqv i × (i ≡ i ⨾ i)

  field
    unital : ∀ x → is-unital x
    assoc  : ∀ {a b c d} (f : hom a b) (g : hom b c) (h : hom c d)
           → f ⨾ (g ⨾ h) ≡ (f ⨾ g) ⨾ h

  idn : ∀ {x} → hom x x
  idn {x} = unital x .fst

  idem : ∀ {x} → idn {x} ≡ idn ⨾ idn
  idem {x} = unital x .snd .snd

{-# INLINE precategory.constructor #-}

module Cat {u v} (C : precategory u v) where
  open precategory C public
  private variable v' w x y z a b c d p' : ob

  module iso-inv {x y} {f : hom x y} (e : is-eqv f) where
    linv : ∀ {z} → hom x z → hom y z
    linv {z} = Equiv.inv ((f ⨾_) , e .fst)

    rinv : ∀ {w} → hom w y → hom w x
    rinv {w} = Equiv.inv ((_⨾ f) , e .snd)

    lunit : hom y y
    lunit = linv f

    runit : hom x x
    runit = rinv f

    pre-counit : ∀ {z} (g : hom x z) → f ⨾ linv g ≡ g
    pre-counit g = Equiv.counit ((f ⨾_) , e .fst) g

    post-counit : ∀ {w} (g : hom w y) → rinv g ⨾ f ≡ g
    post-counit g = Equiv.counit ((_⨾ f) , e .snd) g

    pre-unit : ∀ {z} (g : hom y z) → linv (f ⨾ g) ≡ g
    pre-unit g = Equiv.unit ((f ⨾_) , e .fst) g

    post-unit : ∀ {w} (g : hom w x) → rinv (g ⨾ f) ≡ g
    post-unit g = Equiv.unit ((_⨾ f) , e .snd) g

  idn-is-eqv : ∀ {x} → is-eqv (idn {x})
  idn-is-eqv {x} = unital x .snd .fst

  post-inj : ∀ {e : hom x y} → is-eqv e → {g g' : hom y z} → e ⨾ g ≡ e ⨾ g' → g ≡ g'
  post-inj e {g} {g'} q = sym (iso-inv.pre-unit e g) ∙ ap (iso-inv.linv e) q ∙ iso-inv.pre-unit e g'

  pre-inj : ∀ {e : hom x y} → is-eqv e → {g g' : hom w x} → g ⨾ e ≡ g' ⨾ e → g ≡ g'
  pre-inj e {g} {g'} q = sym (iso-inv.post-unit e g) ∙ ap (iso-inv.rinv e) q ∙ iso-inv.post-unit e g'

  lunit-coherator : ∀ {x} (i : hom x x) → Type (u ⊔ v)
  lunit-coherator {x} i = ∀ {y} (f : hom x y) → i ⨾ (i ⨾ f) ≡ i ⨾ f

  runit-coherator : ∀ {x} (i : hom x x) → Type (u ⊔ v)
  runit-coherator {x} i = ∀ {w} (f : hom w x) → (f ⨾ i) ⨾ i ≡ f ⨾ i

  module idem→coh {x} {i : hom x x} (e : is-eqv i) (p : i ≡ i ⨾ i) where
    open iso-inv e
    lunit-coh : lunit-coherator i
    lunit-coh f = assoc i i f ∙ ap (_⨾ f) (sym p)

    runit-coh : runit-coherator i
    runit-coh f = sym (assoc f i i) ∙ ap (f ⨾_) (sym p)

  module idn {x} {i : hom x x} (e : is-eqv i) (p : i ≡ i ⨾ i) where
    open iso-inv e
    open idem→coh e p

    lneutral : ∀ {y} (f : hom x y) → i ⨾ f ≡ f
    lneutral {y} f t = hcom (∂ t) λ where
      k (t = i0) → pre-unit (i ⨾ f) k
      k (t = i1) → pre-unit f k
      k (k = i0) → linv (lunit-coh f t)

    rneutral : ∀ {w} (f : hom w x) → f ⨾ i ≡ f
    rneutral {w} f t = hcom (∂ t) λ where
      k (t = i0) → post-unit (f ⨾ i) k
      k (t = i1) → post-unit f k
      k (k = i0) → rinv (runit-coh f t)

  module idem→iso-coh {x} {i : hom x x} (e : is-eqv i) (p : i ≡ i ⨾ i) where
    open iso-inv e
    c0 : fiber (i ⨾_) i
    c0 = Equiv.c ((i ⨾_) , e .fst) i
    f0 : Path (fiber (i ⨾_) i) (lunit , pre-counit i) (i , sym p)
    f0 = Equiv.fibers ((i ⨾_) , e .fst) (i , sym p)
    has-rcoh : lunit ≡ i
    has-rcoh = ap fst f0
    f1 : Path (fiber (_⨾ i) i) (runit , post-counit i) (i , sym p)
    f1 = Equiv.fibers ((_⨾ i) , e .snd) (i , sym p)
    has-lcoh : runit ≡ i
    has-lcoh = ap fst f1

  unital-unique : ∀ {x} (u₁ u₂ : is-unital x) → u₁ .fst ≡ u₂ .fst
  unital-unique (i , i-e , i-p) (j , j-e , j-p) =
    sym (idn.rneutral j-e j-p i) ∙ idn.lneutral i-e i-p j

  is-eqv-is-prop : ∀ {x y} (f : hom x y) → is-prop (is-eqv f)
  is-eqv-is-prop f = is-prop-× (Πi-is-prop λ _ → ep) (Πi-is-prop λ _ → ep)
    where ep : ∀ {a b} {g : a → b} → is-prop (is-equiv g)
          ep e₁ e₂ i .eqv-fibers y = is-contr-is-prop _ (e₁ .eqv-fibers y) (e₂ .eqv-fibers y) i

  lunit : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  lunit {x} = idn.lneutral (idn-is-eqv {x}) idem

  runit : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  runit {y = y} = idn.rneutral (idn-is-eqv {y}) idem

  infixr 25 _▹_
  _▹_ : {f f' : hom x y} → f ≡ f' → (h : hom y z) → (f ⨾ h) ≡ (f' ⨾ h)
  γ ▹ h = ap (_⨾ h) γ

  infixl 26 _◃_
  _◃_ : (h : hom w x) → {f f' : hom x y} → f ≡ f' → (h ⨾ f) ≡ (h ⨾ f')
  h ◃ γ = ap (h ⨾_) γ

  nat-sq : {f f' : hom x y} {g g' : hom y z} (α : f ≡ f') (β : g ≡ g')
         → Square (α ▹ g) (f ◃ β) (α ▹ g') (f' ◃ β)
  nat-sq α β i j = α j ⨾ β i

  sect : hom x y → Type v
  sect f = Σ s ∶ hom _ _ , f ⨾ s ≡ idn

  retr : hom x y → Type v
  retr f = Σ r ∶ hom _ _ , r ⨾ f ≡ idn

  is-biinv : hom x y → Type v
  is-biinv f = sect f × retr f

  is-eqv→is-biinv : {f : hom x y} → is-eqv f → is-biinv f
  is-eqv→is-biinv {f = f} p =
    (Equiv.inv ((f ⨾_) , p .fst) idn , Equiv.counit ((f ⨾_) , p .fst) idn) ,
    (Equiv.inv ((_⨾ f) , p .snd) idn , Equiv.counit ((_⨾ f) , p .snd) idn)

  has-triangle : Type (u ⊔ v)
  has-triangle = ∀ {x y z} (f : hom x y) (g : hom y z)
    → assoc f idn g ∙ (runit f ▹ g) ≡ f ◃ lunit g

  has-pentagon : Type (u ⊔ v)
  has-pentagon = ∀ {v' w x y z} (f : hom v' w) (g : hom w x) (h : hom x y) (k : hom y z)
    → (f ◃ assoc g h k) ∙ assoc f (g ⨾ h) k ∙ (assoc f g h ▹ k)
    ≡ assoc f g (h ⨾ k) ∙ assoc (f ⨾ g) h k

  record is-2-coherent : Type (u ⊔ v) where
    no-eta-equality
    field
      triangles : has-triangle
      pentagons : has-pentagon

  {-# INLINE is-2-coherent.constructor #-}

  commutative-sq : (f : hom a b) (g : hom a c) (h : hom b d) (k : hom c d) → Type v
  commutative-sq f g h k = g ⨾ k ≡ f ⨾ h

  id-sq : ∀ {a b} (f : hom a b) → commutative-sq f idn idn f
  id-sq {a} {b} f = lunit f ∙ sym (runit f)

  record is-pullback {f : hom b d} {g : hom c d} {π₁ : hom p' b} {π₂ : hom p' c}
                     (pb : commutative-sq π₁ π₂ f g) : Type (u ⊔ v) where
    no-eta-equality
    field
      universal : ∀ {a} (α : hom a b) (β : hom a c) → commutative-sq α β f g
                → is-contr (Σ h ∶ hom a p' , (h ⨾ π₁ ≡ α) × (h ⨾ π₂ ≡ β))
    gap : ∀ {a} (α : hom a b) (β : hom a c) → commutative-sq α β f g → hom a p'
    gap α β s = universal α β s .center .fst
    gap-π₁ : ∀ {a} (α : hom a b) (β : hom a c) (s : commutative-sq α β f g) → gap α β s ⨾ π₁ ≡ α
    gap-π₁ α β s = universal α β s .center .snd .fst
    gap-π₂ : ∀ {a} (α : hom a b) (β : hom a c) (s : commutative-sq α β f g) → gap α β s ⨾ π₂ ≡ β
    gap-π₂ α β s = universal α β s .center .snd .snd

  {-# INLINE is-pullback.constructor #-}

  record pullback (f : hom b d) (g : hom c d) : Type (u ⊔ v) where
    no-eta-equality
    field
      apex   : ob
      π₁     : hom apex b
      π₂     : hom apex c
      square : commutative-sq π₁ π₂ f g
      is-pb  : is-pullback square
    open is-pullback is-pb public

  {-# INLINE pullback.constructor #-}



record functor {o o' h h'} (C : precategory o h) (D : precategory o' h')
  : Type (o ⊔ o' ⊔ h ⊔ h') where
  no-eta-equality
  private
    module C = Cat C
    module D = Cat D
  field
    ob  : C.ob → D.ob
    map : ∀ {x y} → C.hom x y → D.hom (ob x) (ob y)
    map-eqv  : ∀ {x y} (f : C.hom x y) → C.is-eqv f → D.is-eqv (map f)
    map-comp : ∀ {x y z} (f : C.hom x y) (g : C.hom y z)
             → map (C._⨾_ f g) ≡ D._⨾_ (map f) (map g)

{-# INLINE functor.constructor #-}

module _ {o o' h h'} {C : precategory o h} {D : precategory o' h'} where
  private
    module C = Cat C
    module D = Cat D

  record nat-trans (F G : functor C D) : Type (o ⊔ h ⊔ h') where
    no-eta-equality
    private
      module F = functor F
      module G = functor G
    field
      component : ∀ x → D.hom (F.ob x) (G.ob x)
      natural : ∀ {x y} (f : C.hom x y)
              → D._⨾_ (F.map f) (component y)
              ≡ D._⨾_ (component x) (G.map f)

  {-# INLINE nat-trans.constructor #-}

  _⇒_ : functor C D → functor C D → Type (o ⊔ h ⊔ h')
  _⇒_ = nat-trans

  is-nat-iso : {F G : functor C D} → nat-trans F G → Type (o ⊔ o' ⊔ h')
  is-nat-iso α = ∀ x → D.is-eqv (nat-trans.component α x)

  nat-iso : (F G : functor C D) → Type (o ⊔ o' ⊔ h ⊔ h')
  nat-iso F G = Σ α ∶ nat-trans F G , is-nat-iso α

  record _⊣_ (F : functor C D) (G : functor D C) : Type (o ⊔ o' ⊔ h ⊔ h') where
    no-eta-equality
    private
      module F = functor F
      module G = functor G

    field
      hom-equiv : ∀ x y → D.hom (F.ob x) y ≃ C.hom x (G.ob y)

    adjunct : ∀ {x y} → D.hom (F.ob x) y → C.hom x (G.ob y)
    adjunct {x} {y} = Equiv.fwd (hom-equiv x y)

    coadjunct : ∀ {x y} → C.hom x (G.ob y) → D.hom (F.ob x) y
    coadjunct {x} {y} = Equiv.inv (hom-equiv x y)

    field
      natural-dom : ∀ {x x' y} (f : C.hom x' x) (g : D.hom (F.ob x) y)
                  → adjunct (D._⨾_ (F.map f) g) ≡ C._⨾_ f (adjunct g)
      natural-cod : ∀ {x y y'} (g : D.hom (F.ob x) y) (h : D.hom y y')
                  → adjunct (D._⨾_ g h) ≡ C._⨾_ (adjunct g) (G.map h)

  {-# INLINE _⊣_.constructor #-}

  is-left-adjoint : functor C D → Type (o ⊔ o' ⊔ h ⊔ h')
  is-left-adjoint F = Σ G ∶ functor D C , F ⊣ G

  is-right-adjoint : functor D C → Type (o ⊔ o' ⊔ h ⊔ h')
  is-right-adjoint G = Σ F ∶ functor C D , F ⊣ G

  module _  (F : functor C D) where
    private module F = functor F

    functor-image-unital : ∀ {i} → D.is-unital (F.ob i)
    functor-image-unital .fst = F.map C.idn
    functor-image-unital {i} .snd .fst = F.map-eqv C.idn (C.unital i .snd .fst)
    functor-image-unital .snd .snd = ap F.map C.idem ∙ F.map-comp C.idn C.idn

    id-nat : nat-trans F F
    id-nat .nat-trans.component x = D.idn
    id-nat .nat-trans.natural f = D.runit (F.map f) ∙ sym (D.lunit (F.map f))

    id-nat-iso : is-nat-iso id-nat
    id-nat-iso x = D.idn-is-eqv

  module _ {F G H : functor C D} where
    private
      module F = functor F
      module G = functor G
      module H = functor H

    infixr 30 _⨾ⁿ_
    _⨾ⁿ_ : nat-trans F G → nat-trans G H → nat-trans F H
    (α ⨾ⁿ β) .nat-trans.component x = D._⨾_ (nat-trans.component α x) (nat-trans.component β x)
    (α ⨾ⁿ β) .nat-trans.natural {x} {y} f =
      D.assoc (F.map f) (nat-trans.component α y) (nat-trans.component β y)
      ∙ ap (λ z → D._⨾_ z (nat-trans.component β y)) (nat-trans.natural α f)
      ∙ sym (D.assoc (nat-trans.component α x) (G.map f) (nat-trans.component β y))
      ∙ ap (D._⨾_ (nat-trans.component α x)) (nat-trans.natural β f)
      ∙ D.assoc (nat-trans.component α x) (nat-trans.component β x) (H.map f)

    private
      is-equiv-comp : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
                    → {f : A → B} {g : B → C}
                    → is-equiv f → is-equiv g → is-equiv (g ∘ f)
      is-equiv-comp {f = f} {g = g} ef eg = ((f , ef) ∙e (g , eg)) .snd

    comp-is-eqv : ∀ {a b c} {f : D.hom a b} {g : D.hom b c}
                → D.is-eqv f → D.is-eqv g → D.is-eqv (D._⨾_ f g)
    comp-is-eqv {f = f} {g = g} fe ge .fst {z} =
      subst is-equiv (funext λ h → D.assoc f g h) (is-equiv-comp (ge .fst) (fe .fst))
    comp-is-eqv {f = f} {g = g} fe ge .snd {w} =
      subst is-equiv (funext λ h → sym (D.assoc h f g)) (is-equiv-comp (fe .snd) (ge .snd))

    comp-nat-iso : (α : nat-trans F G) (β : nat-trans G H)
                 → is-nat-iso α → is-nat-iso β → is-nat-iso (α ⨾ⁿ β)
    comp-nat-iso α β α-iso β-iso x = comp-is-eqv (α-iso x) (β-iso x)


```
