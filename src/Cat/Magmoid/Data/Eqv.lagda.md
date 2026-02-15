Lane Biocini
February 2025

Wild equivalences

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Magmoid.Type
import Cat.Magmoid.Data.Neutral as N
import Cat.Magmoid.Data.Unit as U
import Cat.Magmoid.Data.Iso as I

module Cat.Magmoid.Data.Eqv (M : Magmoids) (u : ∀ x → N.unital M x) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan using (pcom; _∙_)
open import Core.Transport
open import Core.Equiv hiding (_≃_)

open import Cat.Magmoid.Data.Base M
open N M

private module unit {x} = U M (u x)
open unit

private module iso = I M u
open iso using (_≅_; is-iso)

module _  {x y} where
  sect : hom x y → Type h
  sect f = Σ s ∶ hom _ _ , f ⨾ s ≡ idn

  retr : hom x y → Type h
  retr f = Σ r ∶ hom _ _ , r ⨾ f ≡ idn

  is-biinv : hom x y → Type h
  is-biinv f = sect f × retr f

  is-neutral→is-biinv : {f : hom x y} → is-neutral f → is-biinv f
  is-neutral→is-biinv {f} p .fst .fst = Equiv.inv ((f ⨾_) , p .snd) idn
  is-neutral→is-biinv {f} p .fst .snd = Equiv.counit ((f ⨾_) , p .snd) idn
  is-neutral→is-biinv {f} p .snd .fst = Equiv.inv ((_⨾ f) , p .fst) idn
  is-neutral→is-biinv {f} p .snd .snd = Equiv.counit ((_⨾ f) , p .fst) idn

  is-neutral→biinv-is-contr
    : {f : hom x y} → is-neutral f → is-contr (is-biinv f)
  is-neutral→biinv-is-contr p =
    is-contr-× (p .snd .eqv-fibers idn)
               (p .fst .eqv-fibers idn)

  is-neutral→biinv-is-embedding
    : {f : hom x y}
    → (bi : is-biinv f)
    → is-prop (fiber (is-neutral→is-biinv {f = f}) bi)
  is-neutral→biinv-is-embedding bi =
    Σ-is-prop
      (is-neutral-is-prop _)
      (λ n → is-contr→is-set
        (is-neutral→biinv-is-contr n) _ _)

_≃_ : ob → ob → Type h
_≃_ x y = Σ f ∶ hom x y , is-biinv f

idn-biinv : ∀ x → is-biinv (idn {x})
idn-biinv x = (idn , idem) , (idn , idem)

eqv-refl : ∀ {x} → x ≃ x
eqv-refl {x} = idn , idn-biinv x

≐→≃ : ∀ {x y} → x ≐ y → x ≃ y
≐→≃ (f , n) = f , is-neutral→is-biinv n

≅→≃ : ∀ {x y} → x ≅ y → x ≃ y
≅→≃ (f , g , p , q) = f , (g , p) , (g , q)

module associator (assoc : associativity) where
  module _ {x y} {f : hom x y} (((s , p) , (r , q)) : is-biinv f) where
    private
      s≡r : s ≡ r
      s≡r = pcom (unitl s) (sym q ▹ s) (pcom (assoc r f s) (r ◃ p) (unitr r))

    private
      f⨾r≡idn : f ⨾ r ≡ idn
      f⨾r≡idn = ap (f ⨾_) (sym s≡r) ∙ p

      s⨾f≡idn : s ⨾ f ≡ idn
      s⨾f≡idn = ap (_⨾ f) s≡r ∙ q

    is-biinv→is-neutral : is-neutral f
    is-biinv→is-neutral .fst = iso→equiv (_⨾ f) (_⨾ r)
      (λ h → pcom (assoc h f r) (h ◃ f⨾r≡idn) (unitr h))
      (λ k → pcom (assoc k r f) (k ◃ q) (unitr k)) .snd
    is-biinv→is-neutral .snd = iso→equiv (f ⨾_) (s ⨾_)
      (λ g → pcom (sym (assoc s f g)) (s⨾f≡idn ▹ g) (unitl g))
      (λ k → pcom (sym (assoc f s k)) (p ▹ k) (unitl k)) .snd

    is-biinv→sect-is-biinv : is-biinv s
    is-biinv→sect-is-biinv .snd = f , p
    is-biinv→sect-is-biinv .fst = f , s⨾f≡idn

    is-biinv→retr-is-biinv : is-biinv r
    is-biinv→retr-is-biinv .fst = f , q
    is-biinv→retr-is-biinv .snd = f , f⨾r≡idn

  is-biinv-is-prop : ∀ {x y} (f : hom x y) → is-prop (is-biinv f)
  is-biinv-is-prop f = inhab-to-contr→is-prop λ bi →
    is-contr-× (is-biinv→is-neutral bi .snd .eqv-fibers idn)
               (is-biinv→is-neutral bi .fst .eqv-fibers idn)

  is-neutral≃is-biinv
    : ∀ {x y} (f : hom x y)
    → Equiv (is-neutral f) (is-biinv f)
  is-neutral≃is-biinv f = iso→equiv
    is-neutral→is-biinv
    (is-biinv→is-neutral {f = f})
    (λ n → is-neutral-is-prop f _ _)
    (λ bi → is-biinv-is-prop f _ _)

  module _ {x y} ((f , s , r) : x ≃ y) where
    private
      s≡r : s .fst ≡ r .fst
      s≡r = pcom (unitl (s .fst)) (sym (r .snd) ▹ (s .fst)) (pcom (assoc (r .fst) f (s .fst)) (r .fst ◃ (s .snd)) (unitr (r .fst)))

    eqv-inv : y ≃ x
    eqv-inv .fst = s .fst
    eqv-inv .snd = is-biinv→sect-is-biinv {f = f} (s , r)

    eqv-inv-retr : y ≃ x
    eqv-inv-retr .fst = r .fst
    eqv-inv-retr .snd = is-biinv→retr-is-biinv {f = f} (s , r)

    eqv-inv≡eqv-inv-retr : eqv-inv ≡ eqv-inv-retr
    eqv-inv≡eqv-inv-retr i .fst = s≡r i
    eqv-inv≡eqv-inv-retr i .snd = is-prop→PathP
      (λ i → is-biinv-is-prop (s≡r i))
      (eqv-inv .snd) (eqv-inv-retr .snd) i

  module _ {x y z}
    ((f , (s0 , p0) , (r0 , q0)) : x ≃ y)
    ((g , (s1 , p1) , (r1 , q1)) : y ≃ z)
    where
    eqv-cat : x ≃ z
    eqv-cat .fst = f ⨾ g
    eqv-cat .snd .fst = s1 ⨾ s0
      , pcom (assoc f g (s1 ⨾ s0))
             (f ◃ assoc g s1 s0)
             (pcom (f ◃ (sym p1 ▹ s0)) (f ◃ unitl s0) p0)
    eqv-cat .snd .snd = r1 ⨾ r0
      , pcom (assoc r1 r0 (f ⨾ g))
             (r1 ◃ assoc r0 f g)
             (pcom (r1 ◃ (sym q0 ▹ g)) (r1 ◃ unitl g) q1)

  ≃→≐ : ∀ {x y} → x ≃ y → x ≐ y
  ≃→≐ (f , bi) = f , is-biinv→is-neutral {f = f} bi

  ≃→≅ : ∀ {x y} → x ≃ y → x ≅ y
  ≃→≅ (f , (s , p) , (r , q)) = f , s , p , s⨾f≡idn where
    s≡r : s ≡ r
    s≡r = pcom (unitl s) (sym q ▹ s) (pcom (assoc r f s) (r ◃ p) (unitr r))
    s⨾f≡idn : s ⨾ f ≡ idn
    s⨾f≡idn = ap (_⨾ f) s≡r ∙ q

  ≐→≅ : ∀ {x y} → x ≐ y → x ≅ y
  ≐→≅ e = ≃→≅ (≐→≃ e)

  ≅→≐ : ∀ {x y} → x ≅ y → x ≐ y
  ≅→≐ e = ≃→≐ (≅→≃ e)

  private
    _*_ = eqv-cat; infixr 40 _*_

  eqv-unitl : ∀ {x y} (e : x ≃ y) → eqv-refl * e ≡ e
  eqv-unitl e i .fst = unitl (e .fst) i
  eqv-unitl e i .snd = is-prop→PathP
    (λ i → is-biinv-is-prop (unitl (e .fst) i))
    ((eqv-refl * e) .snd) (e .snd) i

  eqv-unitr : ∀ {x y} (e : x ≃ y) → e * eqv-refl ≡ e
  eqv-unitr e i .fst = unitr (e .fst) i
  eqv-unitr e i .snd = is-prop→PathP
    (λ i → is-biinv-is-prop (unitr (e .fst) i))
    ((e * eqv-refl) .snd) (e .snd) i

  eqv-assoc : ∀ {w x y z} (e : w ≃ x) (d : x ≃ y) (c : y ≃ z)
    → (e * d) * c ≡ e * (d * c)
  eqv-assoc e d c i .fst = sym (assoc (e .fst) (d .fst) (c .fst)) i
  eqv-assoc e d c i .snd = is-prop→PathP
    (λ i → is-biinv-is-prop (sym (assoc (e .fst) (d .fst) (c .fst)) i))
    (((e * d) * c) .snd) ((e * (d * c)) .snd) i

  module _ {x y} {f : hom x y} (bi : is-biinv f) where
    biinv-loop
      : is-neutral.loop (is-biinv→is-neutral bi) ≡ idn
    biinv-loop = loop-absorb (is-biinv→is-neutral bi)

    biinv-coloop
      : is-neutral.coloop (is-biinv→is-neutral bi) ≡ idn
    biinv-coloop =
      coloop-absorb (is-biinv→is-neutral bi)
