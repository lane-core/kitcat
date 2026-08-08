The diagonal chosen edge: one family `rx` fills both argument slots,
readback aligns the reflection with it, and both cuts are
contractible. This is the framed carrier at the diagonal framing —
the general theory's `rx` and `corx` set equal, both this one edge
— so the frame theory applies verbatim; what the diagonal adds is
the unit package. A unit is a neutral idempotent, its type is
contractible, and the chosen edge is identified with it — from
there the two hands agree and the embedding condition is a theorem, and each
hand is associative and two-sided unital. The two hands agreeing
collapses them to one composition, so the graph carries an
ordinary category: the diagonal framing is exactly the condition
under which the two-hand theory collapses to one.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Diagonal where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Path.Base
open import Core.Equiv.Base
  using (_≃_; is-equiv; is-contr-equiv; iso→equiv; module Equiv)
open import Core.Equiv.Properties
  using (esym; _∙e_; Σ-equiv-snd; bi-inv→equiv; is-equiv-is-prop)
open import Core.Function.Embedding
  using ( equiv→lc; image-fibers-contr→is-embedding
        ; is-embedding→ap-equiv; is-equiv→is-embedding )
open import Core.HLevel.Base using (Πi-is-prop; ×-is-hlevel)
open import Core.Transport.Base using (is-prop→PathP; transport)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr; transport-equiv)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding using (is-representable; reflect-is-embedding)
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Degenerate.Interchange
```

## Neutrality, self-filled

An endomorphism holds its own slot while the other varies. It is
tested against its own object and nothing else, needing no chosen
edge to state, and each half is a proposition.

```agda
module _ {o h} (G : virtual-graph o h) where
  open virtual-graph G

  is-neutral : ∀ {x} → hom x x → Type (o ⊔ h)
  is-neutral {x} e =
      (∀ {z} → is-equiv (λ (k : hom x z) → reflect e ((x , e) , (z , k))))
    × (∀ {w} → is-equiv (λ (g : hom w x) → reflect e ((w , g) , (x , e))))

  is-neutral-is-prop : ∀ {x} (e : hom x x) → is-prop (is-neutral e)
  is-neutral-is-prop e =
    ×-is-hlevel 1 (Πi-is-prop λ _ → is-equiv-is-prop _)
                  (Πi-is-prop λ _ → is-equiv-is-prop _)
```

## The diagonal carrier

```agda
module diagonal {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x)
  (open framing G rx rx)
  (R : readback-of)
  (cc⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (composite⁺ f g)))
  (cc⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (is-representable G (composite⁻ f g)))
  where

  open framed-interchange G rx rx R cc⁺ cc⁻ public
    renaming (unitr⁺ to unitr⁺rx; unitl⁻ to unitl⁻rx)
```

Readback alone gives left-cancellability, with no embedding-condition
hypothesis.

```agda
  reflect-lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc {m = m} {n} p = sym (R m) ∙ ap eval p ∙ R n
```

The two halves of neutrality are the two hands.

```agda
  le-is-coact : ∀ {x} (e : hom x x) {z} (k : hom x z)
              → coact-π (e ⨾⁻ e) (z , k) ≡ reflect e ((x , e) , (z , k))
  le-is-coact {x} e {z} k =
    (λ i → reflect-⨾⁻ e e i (var x , (z , k)))
    ∙ ap (λ t → reflect e (t , (z , k))) (act-var e)

  re-is-act : ∀ {x} (e : hom x x) {w} (g : hom w x)
            → act-π (e ⨾⁺ e) (w , g) ≡ reflect e ((w , g) , (x , e))
  re-is-act {x} e {w} g =
    (λ i → reflect-⨾⁺ e e i ((w , g) , covar x))
    ∙ ap (λ c → reflect e ((w , g) , c)) (coact-covar e)
```

A unit is a neutral idempotent. The predicate is not itself a
proposition — its second component is a path between untruncated
edges — and the type of edges satisfying it is one, proved as
`pinned.is-unital-is-prop` below, so inhabitation is property.

```agda
  unital : ∀ {x} → hom x x → Type (o ⊔ h)
  unital e = is-neutral G e × (e ⨾⁻ e ≡ e)

  is-unital : ob → Type (o ⊔ h)
  is-unital x = Σ e ∶ hom x x , unital e
```

## The unit package

```agda
  module pinned (unit : (x : ob) → is-unital x) where

    idn : ∀ {x} → hom x x
    idn {x} = unit x .fst

    idn-neutral : ∀ {x} → is-neutral G (idn {x})
    idn-neutral {x} = unit x .snd .fst

    idn-idem⁻ : ∀ {x} → idn {x} ⨾⁻ idn ≡ idn
    idn-idem⁻ {x} = unit x .snd .snd
```

The unit's own idempotence turns the first half of its neutrality
into an equivalence of the positive action, hence of `idn ⨾⁺ _`.
Mixed associativity then makes `idn` a left unit for the negative
hand, as `rx` already is, and the second half of neutrality cancels
the two against each other: the diagonal edge is identified with
the extracted unit.

```agda
    idn-pre : ∀ {x z} → is-equiv (λ (k : hom x z) → coact-π idn (z , k))
    idn-pre {x} {z} =
      subst (λ t → is-equiv (λ (k : hom x z) → coact-π t (z , k))) idn-idem⁻
        (subst is-equiv (funext λ k → sym (le-is-coact idn k)) (idn-neutral .fst))

    idn-⨾⁺-equiv : ∀ {x z} → is-equiv (λ (k : hom x z) → idn ⨾⁺ k)
    idn-⨾⁺-equiv {x} {z} =
      subst is-equiv (funext λ k → ⨾⁺-is-coact idn k) idn-pre

    unitl⁻ : ∀ {x z} (m : hom x z) → idn ⨾⁻ m ≡ m
    unitl⁻ {x} {z} m =
        ap (idn ⨾⁻_) (sym p)
      ∙ mixed-assoc idn idn k
      ∙ ap (_⨾⁺ k) idn-idem⁻
      ∙ p
      where
        E : hom x z ≃ hom x z
        E = (λ k → idn ⨾⁺ k) , idn-⨾⁺-equiv

        k : hom x z
        k = Equiv.inv E m

        p : idn ⨾⁺ k ≡ m
        p = Equiv.counit E m

    post-eqv : ∀ {w x} → is-equiv (λ (g : hom w x) → g ⨾⁻ (idn ⨾⁺ idn))
    post-eqv {w} {x} =
      subst is-equiv
        (funext λ g → sym (re-is-act idn g) ∙ ⨾⁻-is-act (idn ⨾⁺ idn) g)
        (idn-neutral .snd)

    rx≡idn : (x : ob) → rx x ≡ idn {x}
    rx≡idn x = equiv→lc post-eqv
      (unitl⁻rx (idn ⨾⁺ idn) ∙ sym (unitl⁻ (idn ⨾⁺ idn)))
```

The other two unit laws.

```agda
    unitr⁺ : ∀ {x y} (f : hom x y) → f ⨾⁺ idn ≡ f
    unitr⁺ {x} {y} f = ap (f ⨾⁺_) (sym (rx≡idn y)) ∙ unitr⁺rx f

    idem⁺ : ∀ {x} → idn {x} ⨾⁺ idn ≡ idn
    idem⁺ = unitr⁺ idn

    coact-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z) (k : coterm z)
             → coact (f ⨾⁺ g) k ≡ coact f (coact g k)
    coact-⨾⁺ f g k i = k .fst , reflect-⨾⁺ f g i (var _ , k)

    idn-post : ∀ {w x} → is-equiv (λ (t : hom w x) → act-π idn (w , t))
    idn-post {w} {x} =
      subst (λ s → is-equiv (λ (t : hom w x) → act-π s (w , t))) idem⁺
        (subst is-equiv (funext λ g → sym (re-is-act idn g)) (idn-neutral .snd))

    absorb⁺ : ∀ {y} (k : coterm y) → coact idn k ≡ k
    absorb⁺ {y} k i = k .fst , π i
      where
        double : coact-π idn (coact idn k) ≡ coact-π idn k
        double =
          sym (ap snd (coact-⨾⁺ idn idn k))
          ∙ ap (λ t → coact t k .snd) idem⁺

        π : coact-π idn k ≡ k .snd
        π = equiv→lc idn-pre double

    absorb⁻ : ∀ {x} (t : term x) → act idn t ≡ t
    absorb⁻ {x} t i = t .fst , π i
      where
        double : act-π idn (act idn t) ≡ act-π idn t
        double =
          sym (ap snd (act-⨾⁻ idn idn t))
          ∙ ap (λ s → act s t .snd) idn-idem⁻

        π : act-π idn t ≡ t .snd
        π = equiv→lc idn-post double

    unitl⁺ : ∀ {x y} (f : hom x y) → idn ⨾⁺ f ≡ f
    unitl⁺ {x} {y} f =
      sym (R (idn ⨾⁺ f))
      ∙ ap eval (reflect-⨾⁺ idn f)
      ∙ ap (λ c → reflect idn (var x , c)) (coact-covar f)
      ∙ ap snd (absorb⁺ (y , f))

    unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ idn ≡ f
    unitr⁻ {x} {y} f =
      sym (R (f ⨾⁻ idn))
      ∙ ap eval (reflect-⨾⁻ f idn)
      ∙ ap (λ t → reflect idn (t , covar y)) (act-var f)
      ∙ ap snd (absorb⁻ (x , f))
```

Interchange is a theorem: mixed associativity at the unit collapses
on both sides, and what is left is the agreement of the two hands.

```agda
    hands-agree : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾⁻ g ≡ f ⨾⁺ g
    hands-agree f g =
      sym (ap (f ⨾⁻_) (unitl⁺ g))
      ∙ mixed-assoc f idn g
      ∙ ap (_⨾⁺ g) (unitr⁻ f)

    judgment-cuts-agree : ∀ {x y z} (f : hom x y) (g : hom y z)
                         → composite⁺ f g ≡ composite⁻ f g
    judgment-cuts-agree f g =
      sym (reflect-⨾⁺ f g)
      ∙ ap reflect (sym (hands-agree f g))
      ∙ reflect-⨾⁻ f g
```

The embedding condition is a theorem: a cut against the unit is the
bare reflection, so each cut's contractible fibre is a contractible
fibre over a point of the image.

```agda
    composite⁻-idn : ∀ {x y} (g : hom x y) → composite⁻ idn g ≡ reflect g
    composite⁻-idn g i γ = reflect g (absorb⁻ (γ .fst) i , γ .snd)

    composite⁺-idn : ∀ {x y} (f : hom x y) → composite⁺ f idn ≡ reflect f
    composite⁺-idn f i γ = reflect f (γ .fst , absorb⁺ (γ .snd) i)

    reflect-image-contr
      : ∀ {x y} (f : hom x y) → is-contr (is-representable G (reflect f))
    reflect-image-contr f =
      subst (λ α → is-contr (is-representable G α)) (composite⁻-idn f) (cc⁻ idn f)

    stable : reflect-is-embedding G
    stable {x} {y} = image-fibers-contr→is-embedding (reflect-image-contr {x} {y})

    contr-representable
      : ∀ {x y} (α : judgment x y)
      → is-representable G α → is-contr (is-representable G α)
    contr-representable α = prop-inhabited→is-contr (stable α)
```

Associativity for the positive hand, from the contractible cut; the
negative hand's is `assoc⁻` of the frame theory above.

```agda
    assoc⁺ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
           → (f ⨾⁺ g) ⨾⁺ h ≡ f ⨾⁺ (g ⨾⁺ h)
    assoc⁺ f g h =
      ap fst (is-contr→is-prop (cc⁺ f (g ⨾⁺ h)) a₁ (cc⁺ f (g ⨾⁺ h) .center))
      where
        a₁ : is-representable G (composite⁺ f (g ⨾⁺ h))
        a₁ = (f ⨾⁺ g) ⨾⁺ h
           , reflect-⨾⁺ (f ⨾⁺ g) h
           ∙ (λ i γ → reflect-⨾⁺ f g i (γ .fst , coact h (γ .snd)))
           ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁺ g h (γ .snd) (~ i)))
```

## The unit is unique

A neutral edge is a composition-action isomorphism, with no
idempotence spent; idempotence is then a based path to the unit, and
the type of neutral idempotents is contractible with the unit as its
centre — the inhabitation parameter is a property.

```agda
    private
      square-equiv→equiv
        : ∀ {u} {A : Type u} {g : A → A}
        → is-equiv (λ a → g (g a)) → is-equiv g
      square-equiv→equiv {g = g} eq = bi-inv→equiv
        ( ((λ b → g (E.inv b)) , λ b → E.counit b)
        , ((λ b → E.inv (g b)) , λ a → E.unit a) )
        where module E = Equiv ((λ a → g (g a)) , eq)

    neutral→pre
      : ∀ {x} (e : hom x x) → is-neutral G e
      → ∀ {z} → is-equiv (λ (k : hom x z) → e ⨾⁺ k)
    neutral→pre {x} e u {z} = square-equiv→equiv
      (subst is-equiv (funext step) (u .fst {z}))
      where
        step : (k : hom x z) → reflect e ((x , e) , (z , k)) ≡ e ⨾⁺ (e ⨾⁺ k)
        step k =
          sym (le-is-coact e k)
          ∙ ⨾⁺-is-coact (e ⨾⁻ e) k
          ∙ ap (_⨾⁺ k) (hands-agree e e)
          ∙ assoc⁺ e e k

    neutral→post
      : ∀ {x} (e : hom x x) → is-neutral G e
      → ∀ {w} → is-equiv (λ (g : hom w x) → g ⨾⁻ e)
    neutral→post {x} e u {w} = square-equiv→equiv
      (subst is-equiv (funext step) (u .snd {w}))
      where
        step : (g : hom w x) → reflect e ((w , g) , (x , e)) ≡ (g ⨾⁻ e) ⨾⁻ e
        step g =
          sym (re-is-act e g)
          ∙ ⨾⁻-is-act (e ⨾⁺ e) g
          ∙ ap (g ⨾⁻_) (sym (hands-agree e e))
          ∙ assoc⁻ g e e

    cancel : ∀ {x} (e : hom x x) → is-neutral G e → e ⨾⁻ e ≡ e → e ≡ idn
    cancel e u p = equiv→lc (neutral→pre e u)
      (sym (hands-agree e e) ∙ p ∙ sym (unitr⁺ e))

    cancel-equiv : ∀ {x} (e : hom x x) (u : is-neutral G e)
                 → (e ⨾⁻ e ≡ e) ≃ (e ≡ idn)
    cancel-equiv {x} e u = esym (ap-pre ∙e shift)
      where
        ap-pre : (e ≡ idn) ≃ (e ⨾⁺ e ≡ e ⨾⁺ idn)
        ap-pre = ap (e ⨾⁺_)
               , is-embedding→ap-equiv
                   (is-equiv→is-embedding (neutral→pre e u))

        P : (e ⨾⁺ e ≡ e ⨾⁺ idn) ≡ (e ⨾⁻ e ≡ e)
        P i = hands-agree e e (~ i) ≡ unitr⁺ e i

        shift : (e ⨾⁺ e ≡ e ⨾⁺ idn) ≃ (e ⨾⁻ e ≡ e)
        shift = transport P , transport-equiv P

    private
      pinned-at : (x : ob) → Type (o ⊔ h)
      pinned-at x = Σ e ∶ hom x x , is-neutral G e × (e ≡ idn)

      pinned-contr : (x : ob) → is-contr (pinned-at x)
      pinned-contr x .center = idn , idn-neutral , refl
      pinned-contr x .paths (e , u , q) i =
          q (~ i)
        , is-prop→PathP (λ j → is-neutral-is-prop G (q (~ j))) idn-neutral u i
        , λ j → q (~ i ∨ j)

    unit-contr : (x : ob) → is-contr (is-unital x)
    unit-contr x =
      is-contr-equiv
        (Σ-equiv-snd λ e → Σ-equiv-snd λ u → cancel-equiv e u)
        (pinned-contr x)

    is-unital-is-prop : (x : ob) → is-prop (is-unital x)
    is-unital-is-prop x = is-contr→is-prop (unit-contr x)
```
