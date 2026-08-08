The Klein four-group under a three-cycle-half-twisted reflection: a
one-object carrier on `Bool × Bool` under componentwise `xor`, with
the reflection reading its edge through a three-cycle `σ` of the
non-unit elements. Every hypothesis of the extraction telescope is
inhabited — the embedding condition, both cuts, both tiers — and
the extraction computes: the extracted positive half-twist is
`ψ v⁻ = v⁺` and the positive tier's centre is `ψ v⁺ = c⁺`, one
further step around the cycle. The two differ in their first component, so the centre
agreement, the term-side cancellation, and op-involutivity at the
half-twist are all refutable here, while right-cancellability of
`_⨾⁻ v⁺` holds — the two ingredients of the readback-record
cancellation reduction come apart on this carrier.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Bool.Klein where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false; module Bool)
open import Core.Data.Empty
open import Core.Kan using (_∙_)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-hlevel; ×-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)

open Bool using (xor; module xor)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Degenerate.Extraction
```

## The group and the cycle

```agda
K : Type
K = Bool × Bool

_⊕_ : K → K → K
w ⊕ v = xor (w .fst) (v .fst) , xor (w .snd) (v .snd)

0₄ v⁻ v⁺ c⁺ : K
0₄ = false , false
v⁻ = false , true
v⁺ = true  , true
c⁺ = true  , false

σ ψ : K → K
σ (false , false) = false , false
σ (false , true)  = true  , false
σ (true  , false) = true  , true
σ (true  , true)  = false , true

ψ (false , false) = false , false
ψ (true  , false) = false , true
ψ (true  , true)  = true  , false
ψ (false , true)  = true  , true

σψ : ∀ w → σ (ψ w) ≡ w
σψ (false , false) = refl
σψ (false , true)  = refl
σψ (true  , false) = refl
σψ (true  , true)  = refl

ψσ : ∀ w → ψ (σ w) ≡ w
ψσ (false , false) = refl
ψσ (false , true)  = refl
ψσ (true  , false) = refl
ψσ (true  , true)  = refl

σ-inj : {x y : K} → σ x ≡ σ y → x ≡ y
σ-inj {x} {y} p = sym (ψσ x) ∙ ap ψ p ∙ ψσ y

⊕-assoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc a b c i =
    xor.assoc (a .fst) (b .fst) (c .fst) (~ i)
  , xor.assoc (a .snd) (b .snd) (c .snd) (~ i)

⊕-invol : ∀ a x → a ⊕ (a ⊕ x) ≡ x
⊕-invol a x i = xor.invol (a .fst) (x .fst) i , xor.invol (a .snd) (x .snd) i

⊕-unitr : ∀ a → a ⊕ 0₄ ≡ a
⊕-unitr a i = xor.unitr (a .fst) i , xor.unitr (a .snd) i

⊕-comm : ∀ a b → a ⊕ b ≡ b ⊕ a
⊕-comm a b i = xor.comm (a .fst) (b .fst) i , xor.comm (a .snd) (b .snd) i

⊕-cancel-l : ∀ a {x y} → a ⊕ x ≡ a ⊕ y → x ≡ y
⊕-cancel-l a {x} {y} p = sym (⊕-invol a x) ∙ ap (a ⊕_) p ∙ ⊕-invol a y

⊕-cancel-r : ∀ a {x y} → x ⊕ a ≡ y ⊕ a → x ≡ y
⊕-cancel-r a {x} {y} p = ⊕-cancel-l a (⊕-comm a x ∙ p ∙ ⊕-comm y a)

K-set : is-set K
K-set = ×-is-hlevel 2 Bool.set Bool.set
```

## The carrier

The reflection reads the string through `σ`. Injectivity of each
action map comes from cancelling the flanks and inverting `σ`, each
tier's centre is the `ψ`-image its side's equation names, and both
cuts are represented by `ψ` of the gathered middle.

```agda
KM : virtual-graph 0ℓ 0ℓ
KM .virtual-graph.ob      = ⊤
KM .virtual-graph.hom _ _ = K
KM .virtual-graph.reflect m γ = γ .fst .snd ⊕ (σ m ⊕ γ .snd .snd)

cπ : K → Sigma ⊤ (λ _ → K) → K
cπ m k = v⁻ ⊕ (σ m ⊕ k .snd)

aπ : K → Sigma ⊤ (λ _ → K) → K
aπ m t = t .snd ⊕ (σ m ⊕ v⁺)

rf : K → Sigma ⊤ (λ _ → K) × Sigma ⊤ (λ _ → K) → K
rf m γ = γ .fst .snd ⊕ (σ m ⊕ γ .snd .snd)

cπ-inj : {m n : K} → cπ m ≡ cπ n → m ≡ n
cπ-inj {m} {n} p =
  σ-inj ( sym (⊕-unitr (σ m))
        ∙ ⊕-cancel-l v⁻ (happly p (tt , 0₄))
        ∙ ⊕-unitr (σ n) )

aπ-inj : {m n : K} → aπ m ≡ aπ n → m ≡ n
aπ-inj {m} {n} p = σ-inj (⊕-cancel-r v⁺ (⊕-cancel-l 0₄ (happly p (tt , 0₄))))

rf-inj : {m n : K} → rf m ≡ rf n → m ≡ n
rf-inj {m} {n} p =
  σ-inj ( sym (⊕-unitr (σ m))
        ∙ ⊕-cancel-l 0₄ (happly p ((tt , 0₄) , (tt , 0₄)))
        ∙ ⊕-unitr (σ n) )

tier⁻ : is-contr (fiber cπ snd)
tier⁻ = prop-inhabited→is-contr
  (injective→is-embedding (Π-is-hlevel 2 λ _ → K-set) cπ cπ-inj snd)
  (v⁺ , funext λ k → ⊕-invol v⁻ (k .snd))

tier⁺ : is-contr (fiber aπ snd)
tier⁺ = prop-inhabited→is-contr
  (injective→is-embedding (Π-is-hlevel 2 λ _ → K-set) aπ aπ-inj snd)
  (c⁺ , funext λ t → ⊕-unitr (t .snd))

S : reflect-is-embedding KM
S = embedding-from-injective KM (λ {_} {_} → K-set) (λ {_} {_} → rf-inj)

cut⁺ : framing⁻.is-composable⁺ KM (λ _ → v⁻)
cut⁺ f g = ψ (σ f ⊕ (v⁻ ⊕ σ g)) , funext λ γ →
  ap (γ .fst .snd ⊕_)
    ( ap (_⊕ γ .snd .snd) (σψ (σ f ⊕ (v⁻ ⊕ σ g)))
    ∙ ⊕-assoc (σ f) (v⁻ ⊕ σ g) (γ .snd .snd)
    ∙ ap (σ f ⊕_) (⊕-assoc v⁻ (σ g) (γ .snd .snd)) )

cut⁻ : framing⁺.is-composable⁻ KM (λ _ → v⁺)
cut⁻ f g = ψ ((σ f ⊕ v⁺) ⊕ σ g) , funext λ γ →
  ap (γ .fst .snd ⊕_)
    ( ap (_⊕ γ .snd .snd) (σψ ((σ f ⊕ v⁺) ⊕ σ g))
    ∙ ⊕-assoc (σ f ⊕ v⁺) (σ g) (γ .snd .snd) )
  ∙ sym (⊕-assoc (γ .fst .snd) (σ f ⊕ v⁺) (σ g ⊕ γ .snd .snd))
```

## The extraction, run at the model

The extraction telescope is inhabited entire: the negative tier's
centre is `v⁺`, and `system⁻`'s positive centre is `c⁺`.

```agda
open extraction KM (λ _ → v⁻) (λ _ → tier⁻)
open extraction.system⁻ KM (λ _ → v⁻) (λ _ → tier⁻) S cut⁺ cut⁻ (λ _ → tier⁺)

is-true : Bool → Type
is-true true  = ⊤
is-true false = ⊥

no-agree : agree → ⊥
no-agree a = subst (λ w → is-true (w .fst)) (a tt) tt

no-cancel⁺ : cancel⁺ → ⊥
no-cancel⁺ c = no-agree (cancel⁺→agree c)
```

Right-cancellability of `_⨾⁻ v⁺` holds — the hand is a composite of
injections — while the frame law `v⁻ ⨾⁻ v⁺ ≡ v⁺` lands on the unit
of the group instead of the extracted half-twist.

```agda
open tower⁻ KM (λ _ → v⁺) S cut⁻ using (_⨾⁻_)

⨾⁻corx-cancellable : {a b : K} → a ⨾⁻ v⁺ ≡ b ⨾⁻ v⁺ → a ≡ b
⨾⁻corx-cancellable {a} {b} p =
  σ-inj (⊕-cancel-r v⁺ (⊕-cancel-r v⁻
    (sym (σψ ((σ a ⊕ v⁺) ⊕ v⁻)) ∙ ap σ p ∙ σψ ((σ b ⊕ v⁺) ⊕ v⁻))))

no-frame⁻ : v⁻ ⨾⁻ v⁺ ≡ v⁺ → ⊥
no-frame⁻ p = subst (λ w → is-true (w .fst)) (sym p) tt
```
