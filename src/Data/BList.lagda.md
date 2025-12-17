Braided lists as a HIT

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.BList where

open import Lib.Core.Prim
open import Lib.Sigma
open import Data.Nat
open import Lib.Core.Base
open import Lib.Core.Kan hiding (fill)
open import Lib.Equiv
open import Lib.Path as Path
open import Lib.Path.Gpd renaming (module cat to cat; cat to infixr 40 _∙_)
open import Lib.Path.Homotopy

private variable u v : Level; A : Type u
infixr 6 _∷_

data Grp {u} (A : Type u) : Type u where
  [] : Grp A
  _∷_ : A → Grp A → Grp A
  ext : ∀ t xs → xs ≡ t ∷ xs
  conj : ∀ t xs → ap (t ∷_) (ext t xs) ≡ ext t (t ∷ xs)

ind : ∀ {u v} {A : Type u} (P : Grp A → Type v)
    → P []
    → (s : ∀ x ws → P ws → P (x ∷ ws))
    → (e : ∀ t ws (a : P ws) → a ≡ s t ws a :: λ i → P (ext t ws i))
    → (∀ t ws (a : P ws) →
         (λ i → s t (ext t ws i) (e t ws a i)) ≡ (e t (t ∷ ws) (s t ws a))
         :: λ i → s t ws a ≡ s t (t ∷ ws) (s t ws a)
         :: λ j → P (conj t ws i j))
    → (ws : Grp A) → P ws
ind P b s e c [] = b
ind P b s e c (x ∷ ws) = s x ws (ind P b s e c ws)
ind P b s e c (ext t ws i) = e t ws (ind P b s e c ws) i
ind P b s e c (conj t ws i j) = c t ws (ind P b s e c ws) i j

center : (t : A) (xs ws : Grp A) (a : xs ≡ ws)
  → PathP (λ i → xs ≡ ext t ws i) a (a ∙ ext t ws)
center t xs ws a i j = hcomp (∂ j ∨ ~ i) λ where
  k (j = i0) → a (~ i ∧ ~ k)
  k (j = i1) → ext t ws (i ∧ k)
  k (i = i0) → a (j ∨ ~ k)
  k (k = i0) → a (j ∨ ~ i)

private module _ (t : A) (xs ws : Grp A) (p : xs ≡ ws) where
  q = p ∙ ext t ws
  e = ext t ws

  φ : PathP (λ i → xs ≡ ext t ws i) p (p ∙ ext t ws)
  φ = center t xs ws p

  θ : erfl xs ≡ ext t ws :: λ i → p i ≡ (p ∙ ext t ws) i
  θ i j = φ j i

  composite : p ∙ ext t ws , θ ≡ p ∙ ext t ws , cat.fill p e
  composite = Composite.unique (erfl xs) p e (p ∙ e , θ)  (p ∙ e , cat.fill p (ext t ws))

  θ' : erfl xs ≡ ext t ws :: λ i → p i ≡ (p ∙ ext t ws) i
  θ' i j = composite i .snd i j

  coh : SquareP (λ i j → p j ≡ composite i .fst j) θ rfl θ' (erfl (ext t ws))
  coh i = composite i .snd

  fcomp : Square (erfl xs) p (ext t ws) (p ∙ ext t ws)
  fcomp i = composite i .snd i

eqv : (x : A) → is-equiv (x ∷_)
eqv x .is-equiv.contr ws .ctr = ws , hsym (ext x ws)
eqv x .is-equiv.contr ws .paths (xs , p) i .fst = hcomp (∂ i) λ where
  k (i = i0) → ws
  k (k = i0) → hsym p i
  k (i = i1) → ext x xs (~ k)
eqv x .is-equiv.contr ws .paths (xs , p) i .snd j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → ext x (p k) (~ j)
  k (i = i1) → conn (ap (x ∷_) (hsym (ext x xs))) p j k
  k (j = i0) → x ∷ cat.cfill (hsym p) (hsym (ext x xs)) i k
  k (j = i1) → p k
  k (k = i0) → conj x xs (~ i) (~ j)

icons : A → Grp A → Grp A
icons a = is-equiv.inv (eqv a)

qinv : (a : A) → is-qinv (a ∷_)
qinv a = record { inv = icons a ; sec = is-equiv.sec (eqv a) ; retr = is-equiv.retr (eqv a) }

cf : (a : A) (ws : Grp A) → is-contr (fiber (_∷_ a) ws)
cf a ws = is-equiv.contr (eqv a) ws

c : (a : A) (ws : Grp A) → Grp A
c a ws = cf a ws .ctr .fst

pa : (a : A) (ws : Grp A) → a ∷ ws ≡ ws
pa a ws = cf a ws .ctr .snd

fpaths : (a : A) (ws : Grp A)
       → ((xs , p) : fiber (a ∷_) ws)
       → ws , hsym (ext a ws) ≡ xs , p
fpaths {A} a ws = cf a ws .paths

contr : (ws : Grp A) → [] ≡ ws
contr {A = A} [] = rfl
contr {A = A} (x ∷ ws) = contr ws ∙ ext x ws
contr {A = A} (ext t ws i) j = cat.fill (contr ws) (ext t ws) j i
contr {A = A} (conj t ws i j) k = hcomp (∂ i ∨ ∂ j ∨ ∂ k) λ where
  l (i = i0) → {!!}
  l (i = i1) → {!!}
  l (j = i0) → {!!}
  l (j = i1) → {!!} -- cat.fill {!s1!} (conj t ws k) k l    -- ({!θ ? ? ? (contr ws) i k!} ∙ {!!}) l
  l (k = i0) → {!!}
  l (k = i1) → {!!}
  l (l = i0) → {!!} where
  s0 : PathP (λ i₁ → contr ws i₁ ≡ (contr ws ∙ ext t ws) i₁) (erfl []) (ext t ws)
  s0 = θ t [] ws (contr ws)

  s1 : PathP (λ i₁ → contr ws i₁ ≡ (contr ws ∙ ext t ws) i₁) (erfl []) (ext t ws)
  s1 = θ' t [] ws (contr ws)

  ρ : SquareP
       (λ i j → contr ws j ≡ composite t [] ws (contr ws) i .fst j)
       s0 rfl s1 (erfl (ext t ws))
  ρ = coh t [] ws (contr ws)

  ι : SquareP
       (λ i₁ j₁ →
          (contr ws ∙ ext t ws) j₁ ≡
          composite t [] (t ∷ ws) (contr ws ∙ ext t ws) i₁ .fst j₁)
       (θ t [] (t ∷ ws) (contr ws ∙ ext t ws)) rfl
       (θ' t [] (t ∷ ws) (contr ws ∙ ext t ws)) (erfl (ext t (t ∷ ws)))
  ι = coh t [] (t ∷ ws) (contr ws ∙ ext t ws)




  -- β : (t : A) (ws : Grp A) (a : [] ≡ ws) →
  --   SquareP (λ i j → [] ≡ conj t ws i j)
  --   (λ i → α t ws a i ∙ ext t (ext t ws i)) rfl
  --   (α t (t ∷ ws) (a ∙ ext t ws)) rfl
  -- β t ws a i j k = hcomp (∂ k ∨ ∂ j ∨ ∂ i) λ where
  --   l (i = i0) → {!!}
  --   l (i = i1) → {!!}
  --   l (j = i0) → {!!}
  --   l (j = i1) → {!!}
  --   l (k = i0) → {!!}
  --   l (k = i1) → {!!}
  --   l (l = i0) → α t (ext t ws k) (α t ws a k) i j



map : {B : Type v} → (A → B) → Grp A → Grp B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
map f (ext t xs i) = ext (f t) (map f xs) i
map f (conj t xs i j) = conj (f t) (map f xs) i j

-- contr-paths : (ws : Grp A) → [] ≡ ws
-- contr-paths [] = rfl
-- contr-paths (x ∷ ws) = ext x [] ∙ ap (x ∷_) (contr-paths ws)
-- contr-paths (ext t ws i) j = {!!}

-- contr-paths (conj t ws i i₁) = {!!}

-- Grp-contr : is-contr (Grp A)
-- Grp-contr .ctr = []
-- Grp-contr .paths ws = contr-paths ws
```
private module test where
  private variable u : Level; A : Type u
  infixr 6 _∷_
  data BList {u} (A : Type u) : Type u where
    [] : BList A
    _∷_ : A → BList A → BList A
    sub : ∀ t x xs → x ∷ xs ≡ t ∷ xs
    yank : ∀ x xs → sub x x xs ≡ erfl (x ∷ xs)

  cons : A → BList A → BList A
  icons : A → BList A → BList A

  cons a [] = [] 
  cons a (x ∷ ws) = a ∷ x ∷ ws
  cons a (sub t x ws i) = a ∷ sub t x ws i
  cons a (yank x ws i j) = a ∷ yank x ws i j

  icons a [] = []
  icons a (x ∷ ws) = {!!}
  icons a (sub t x ws i) = {!!}
  icons a (yank x ws i i₁) = {!!}

  BList-free-∞-group : (x : A) → is-equiv (cons x)
  BList-free-∞-group x .is-equiv.contr [] .ctr = [] , rfl
  BList-free-∞-group x .is-equiv.contr (x₁ ∷ []) .ctr = {!!}
  BList-free-∞-group x .is-equiv.contr (x₁ ∷ x₂ ∷ ws) .ctr = {!!}
  BList-free-∞-group x .is-equiv.contr (x₁ ∷ sub t x₂ ws i) .ctr = {!!}
  BList-free-∞-group x .is-equiv.contr (x₁ ∷ yank x₂ ws i i₁) .ctr = {!!}
  BList-free-∞-group x .is-equiv.contr (sub t x₁ ws i) .ctr = {!!}
  BList-free-∞-group x .is-equiv.contr (yank x₁ ws i i₁) .ctr = {!!}
  BList-free-∞-group x .is-equiv.contr ws .paths = {!!}

  cosub : ∀ t x (xs : BList A) → t ∷ xs ≡ x ∷ xs
  cosub t x xs i = sub t x xs (~ i)
  {-# INLINE cosub #-}
  {-# DISPLAY hsym (sub t x xs) = cosub t x xs #-}

  ind : ∀ {u v} {A : Type u} (P : BList A → Type v)
      → P []
      → (s : ∀ x xs → P xs → P (x ∷ xs))
      → (q : ∀ t x xs (a : P xs) → s x xs a ≡ s t xs a :: λ i → P (sub t x xs i))
      → (∀ x xs (a : P xs)
           → q x x xs a ≡ rfl
           :: λ i → s x xs a ≡ s x xs a
           :: λ j → P (yank x xs i j))
      → ∀ xs → P xs
  ind P b s q h [] = b
  ind P b s q h (x ∷ xs) = s x xs (ind P b s q h xs)
  ind P b s q h (sub t x xs i) = q t x xs (ind P b s q h xs) i
  ind P b s q h (yank x xs i j) = h x xs (ind P b s q h xs) i j

  rec : ∀ {u v} {A : Type u} {B : Type v}
      → (b : B) (f : A → B → B)
      → (q : ∀ x y b → f x b ≡ f y b)
      → (h : ∀ x b → q x x b ≡ rfl)
      → BList A → B
  rec {B} b f q h =
    ind (λ _ → B) b
      (λ x ws b → f x b)
      (λ t x ws a → q x t a)
      λ x xs b → h x b

  _++_ : BList A → BList A → BList A
  [] ++ bs = bs
  (x ∷ as) ++ bs = x ∷ as ++ bs
  sub t x as i ++ bs = sub t x (as ++ bs) i
  yank x as i j ++ bs = yank x (as ++ bs) i j

  unitr : ∀ (ws : BList A) → ws ++ [] ≡ ws
  unitr = ind (λ z → (z ++ []) ≡ z) rfl
    (λ x xs p → ap (x ∷_) p) (λ t x xs p i j → sub t x (p j) i)
    λ x xs p i j k → yank x (p k) i j

  map : ∀ {v} {B : Type v} → (A → B) → BList A → BList B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs
  map f (sub t x xs i) = sub (f t) (f x) (map f xs) i
  map f (yank x xs i j) = yank (f x) (map f xs) i j

  cut : ∀ t x (ws : BList A) → sub t x ws ∙ cosub t x ws ≡ rfl
  cut t x ws = cat.invr (sub t x ws)

  bcat : ∀ {x0 x1 t0 t1}
       → (∀ (xs : BList A) → x0 ∷ xs ≡ t0 ∷ xs)
       → (∀ (xs : BList A) → x1 ∷ xs ≡ t1 ∷ xs)
       → ∀ (ws : BList A) → x1 ∷ x0 ∷ ws ≡ t1 ∷ t0 ∷ ws
  bcat {x0} {x1} {t0} {t1} p q ws = braid q (p ws)

  twist : ∀ x y (ws : BList A) → x ∷ y ∷ ws ≡ y ∷ x ∷ ws
  twist x y ws i = sub y x (sub x y ws i) i
  {-# DISPLAY sub x y (sub y x ws i) i = twist y x ws i #-}

  untwist : ∀ x y (xs : BList A)
          → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  untwist x y xs = hsym (twist y x xs)

  _▷_ : ∀ a b (ws : BList A) → a ∷ b ∷ ws ≡ b ∷ a ∷ ws
  _▷_ a b = bcat (sub a b) (sub b a)

  _◁_ : ∀ a b (ws : BList A) → b ∷ ws ≡ a ∷ ws
  _◁_ a b ws i = cat2 (sub b a ws) (sub b a ws) (sub a b ws) i

  sub-square
    : ∀ t0 x0 t1 x1 (ws : BList A)
    → Square
       (sub t0 x0 (x1 ∷ ws))
       (ap (x0 ∷_) (sub t1 x1 ws))
       (sub t0 x0 (t1 ∷ ws))
       (ap (t0 ∷_) (sub t1 x1 ws))
  sub-square t0 x0 t1 x1 ws =
    braid.htpy (x0 ∷_) (t0 ∷_) (sub t0 x0) (sub t1 x1 ws)

  module bcat where

  brefl : ∀ x (ws : BList A) → x ∷ ws ≡ x ∷ ws
  brefl x ws _ = x ∷ ws
  {-# INLINE brefl #-}

  private module naive where
    bflip : BList A → BList A
    bflip [] = []
    bflip (x ∷ []) = x ∷ []
    bflip (x ∷ y ∷ ws) = y ∷ x ∷ ws
    bflip (x ∷ sub t y ws i) = bcat (brefl x) (sub t y) ws i
    bflip (x ∷ yank y ws i j) = yank y (x ∷ ws) i j
    bflip (sub t x [] i) = sub t x [] i
    bflip (sub t x (z ∷ ws) i) = z ∷ sub t x ws i
    bflip (sub t0 x0 (sub t1 x1 ws i) j) = sub t1 x1 (sub t0 x0 ws j) i
    bflip (sub t x (yank y ws i j) k) = yank y (sub t x ws k) i j
    bflip (yank x [] i j) = yank x [] i j
    bflip (yank x (y ∷ ws) i j) = y ∷ yank x ws i j
    bflip (yank x (sub t y ws i) j k) = sub t y (yank x ws j k) i
    bflip (yank x (yank y ws i j) k l) = yank y (yank x ws k l) i j

    -bflip : BList A → BList A
    -bflip [] = []
    -bflip (x ∷ []) = x ∷ []
    -bflip (x ∷ y ∷ ws) = y ∷ x ∷ ws
    -bflip (x ∷ sub t x0 ws i) = cosub x0 t (x ∷ ws) i
    -bflip (x ∷ yank y ws i j) = yank y (x ∷ ws) i (~ j)
    -bflip (sub t x [] i) = sub x t [] (~ i)
    -bflip (sub t x (y ∷ ws) i) = y ∷ cosub x t ws i
    -bflip (sub t0 x0 (sub t1 x1 ws i) j) = cosub x1 t1 (cosub x0 t0 ws j) i
    -bflip (sub t x (yank y ws i j) k) = yank y (cosub x t ws k) i (~ j)
    -bflip (yank x [] i j) = yank x [] i (~ j)
    -bflip (yank x (y ∷ ws) i j) = y ∷ yank x ws i (~ j)
    -bflip (yank x (sub t x0 ws i) j k) = cosub x0 t (yank x ws j (~ k)) i
    -bflip (yank x (yank y ws i j) k l) = yank y (yank x ws k (~ l)) i (~ j)

    -- bare bflip embeds symmetric monoidal structure
    sym : (ws : BList A) → bflip (bflip ws) ≡ ws
    sym [] = rfl
    sym (x ∷ []) = rfl
    sym (x ∷ y ∷ ws) = rfl
    sym (x ∷ sub t x0 [] i) = rfl
    sym (x ∷ sub t x0 (x₁ ∷ ws) i) = rfl
    sym (x ∷ sub t x0 (sub t₁ x₁ ws i₁) i) = rfl
    sym (x ∷ sub t x0 (yank x₁ ws i₁ i₂) i) = rfl
    sym (x ∷ yank x₁ [] i j) = rfl
    sym (x ∷ yank x₁ (x₂ ∷ ws) i j) = rfl
    sym (x ∷ yank x₁ (sub t x₂ ws i₁) i j) = rfl
    sym (x ∷ yank x₁ (yank x₂ ws i₁ i₂) i j) = rfl
    sym (sub t x [] i) = rfl
    sym (sub t x (x₁ ∷ ws) i) = rfl
    sym (sub t x (sub t₁ x₁ [] i₁) i) = rfl
    sym (sub t x (sub t₁ x₁ (x₂ ∷ ws) i₁) i) = rfl
    sym (sub t x (sub t₁ x₁ (sub t₂ x₂ ws i₂) i₁) i) = rfl
    sym (sub t x (sub t₁ x₁ (yank x₂ ws i₂ i₃) i₁) i) = rfl
    sym (sub t x (yank x₁ [] i₁ i₂) i) = rfl
    sym (sub t x (yank x₁ (x₂ ∷ ws) i₁ i₂) i) = rfl
    sym (sub t x (yank x₁ (sub t₁ x₂ ws i₃) i₁ i₂) i) = rfl
    sym (sub t x (yank x₁ (yank x₂ ws i₃ i₄) i₁ i₂) i) = rfl
    sym (yank x [] i i₁) = rfl
    sym (yank x (x₁ ∷ ws) i i₁) = rfl
    sym (yank x (sub t x₁ [] i₂) i i₁) = rfl
    sym (yank x (sub t x₁ (x₂ ∷ ws) i₂) i i₁) = rfl
    sym (yank x (sub t x₁ (sub t₁ x₂ ws i₃) i₂) i i₁) = rfl
    sym (yank x (sub t x₁ (yank x₂ ws i₃ i₄) i₂) i i₁) = rfl
    sym (yank x (yank x₁ [] i₂ i₃) i i₁) = rfl
    sym (yank x (yank x₁ (x₂ ∷ ws) i₂ i₃) i i₁) = rfl
    sym (yank x (yank x₁ (sub t x₂ ws i₄) i₂ i₃) i i₁) = rfl
    sym (yank x (yank x₁ (yank x₂ ws i₄ i₅) i₂ i₃) i i₁) = rfl

    -- _▹_ : {x0 x1 t0 t1 : A}
    --     → (∀ ws → x0 ∷ ws ≡ t0 ∷ ws)
    --     → (∀ ws → x1 ∷ ws ≡ t1 ∷ ws)
    --     → ∀ ws → x1 ∷ x0 ∷ ws ≡ t0 ∷ t1 ∷ ws
    -- _▹_ {x0} {x1} {t0} {t1} f g ws i = hcomp (∂ i) λ where
    --   k (i = i0) → x1 ∷ f {!!} i
    --   k (k = i0) → {!!}
    --   k (i = i1) → {!!}

    -- cross : ∀ {x0 x1 t0 t1} {ws : BList A}
    --       → x0 ∷ {!!} ∷ ws ≡ t0 ∷ {!!} ∷ ws
    --       → x1 ∷ ws ≡ t1 ∷ ws
    --       → x1 ∷ x0 ∷ ws ≡ t0 ∷ t1 ∷ ws
    -- cross p q i = cat2 {!p!} (braid) q) {!!} i

    -- σ : BList A → BList A
    -- σ [] = []
    -- σ (x ∷ []) = x ∷ []
    -- σ (x ∷ y ∷ ws) = y ∷ x ∷ ws
    -- σ (a ∷ sub t x0 ws i) = hcomp (∂ i) λ where
    --   k (i = i0) → twist a x0 ws k
    --   k (k = i0) → a ∷ sub t x0 ws i
    --   k (i = i1) → twist a t ws k
    -- σ (x ∷ yank y ws i j) = hcomp (∂ i ∨ ∂ j) λ where
    --   k (j = i0) → twist x y ws k
    --   k (j = i1) → twist x y ws k
    --   k (i = i0) → cat2.fill (twist x y ws) (ap (x ∷_) (sub y y ws)) (twist x y ws) j k
    --   k (i = i1) → twist x y ws k
    --   k (k = i0) → x ∷ yank y ws i j
    -- σ (sub t x [] i) = sub t x [] i
    -- σ (sub t x (y ∷ ws) i) = y ∷ (sub t x ws i)
    -- -- (t :> x) :> y =
    -- σ (sub t0 x0 (sub t1 x1 ws i) j) = {!!}
    -- σ (sub t x (yank x₁ ws i₁ i₂) i) = {!!}
    -- σ (yank x ws i i₁) = {!!}

    -- -σ : BList A → BList A
    -- -σ = {!!}

    -- invr : (ws : BList A) → σ (-σ ws) ≡ ws
    -- invr [] = rfl
    -- invr (x ∷ []) = rfl
    -- invr (x ∷ y ∷ ws) = rfl
    -- invr (x ∷ sub t x₁ [] i) = rfl
    -- invr (x ∷ sub t x₁ (x₂ ∷ ws) i) = rfl
    -- invr (x ∷ sub t x₁ (sub t₁ x₂ ws i₁) i) = rfl
    -- invr (x ∷ sub t x₁ (yank x₂ ws i₁ i₂) i) = rfl
    -- invr (x ∷ yank x₁ [] i i₁) = rfl
    -- invr (x ∷ yank x₁ (x₂ ∷ ws) i i₁) = rfl
    -- invr (x ∷ yank x₁ (sub t x₂ ws i₂) i i₁) = rfl
    -- invr (x ∷ yank x₁ (yank x₂ ws i₂ i₃) i i₁) = rfl
    -- invr (sub t x [] i) = rfl
    -- invr (sub t x (x₁ ∷ ws) i) = rfl
    -- invr (sub t x (sub t₁ x₁ [] i₁) i) = rfl
    -- invr (sub t x (sub t₁ x₁ (x₂ ∷ ws) i₁) i) = rfl
    -- invr (sub t x (sub t₁ x₁ (sub t₂ x₂ ws i₂) i₁) i) = rfl
    -- invr (sub t x (sub t₁ x₁ (yank x₂ ws i₂ i₃) i₁) i) = rfl
    -- invr (sub t x (yank x₁ [] i₁ i₂) i) = rfl
    -- invr (sub t x (yank x₁ (x₂ ∷ ws) i₁ i₂) i) = rfl
    -- invr (sub t x (yank x₁ (sub t₁ x₂ ws i₃) i₁ i₂) i) = rfl
    -- invr (sub t x (yank x₁ (yank x₂ ws i₃ i₄) i₁ i₂) i) = rfl
    -- invr (yank x [] i i₁) = rfl
    -- invr (yank x (x₁ ∷ ws) i i₁) = rfl
    -- invr (yank x (sub t x₁ [] i₂) i i₁) = rfl
    -- invr (yank x (sub t x₁ (x₂ ∷ ws) i₂) i i₁) = rfl
    -- invr (yank x (sub t x₁ (sub t₁ x₂ ws i₃) i₂) i i₁) = rfl
    -- invr (yank x (sub t x₁ (yank x₂ ws i₃ i₄) i₂) i i₁) = rfl
    -- invr (yank x (yank x₁ [] i₂ i₃) i i₁) = rfl
    -- invr (yank x (yank x₁ (x₂ ∷ ws) i₂ i₃) i i₁) = rfl
    -- invr (yank x (yank x₁ (sub t x₂ ws i₄) i₂ i₃) i i₁) = rfl
    -- invr (yank x (yank x₁ (yank x₂ ws i₄ i₅) i₂ i₃) i i₁) = rfl

    bflip2 : BList A → BList A
    bflip2 [] = []
    bflip2 (x ∷ ws) = x ∷ bflip ws
    bflip2 (sub t x ws i) = sub t x (bflip ws) i
    bflip2 (yank x ws i j) = yank x (bflip ws) i j

    -- bcat-sq : ∀ x0 x1 x2 (ws : BList A) →
    --   Square
    --     (bcat (sub x2 x0) (sub x0 x2) ws)
    --     (bcat (brefl x0) (sub x1 x2) ws)
    --     (bcat (sub x1 x0) (sub x0 x1) ws)
    --     (bcat (sub x1 x2) (brefl x0) ws)
    -- bcat-sq {A} x0 x1 x2 ws i j =
    --   {!!}

    -- yang-baxter : (ws : BList A) → bflip2 (bflip (bflip2 ws)) ≡ bflip (bflip2 (bflip ws))
    -- yang-baxter [] = rfl
    -- yang-baxter (x ∷ []) i = x ∷ []
    -- yang-baxter (x ∷ y ∷ []) i = bcat (sub y x) (sub x y) [] i
    -- yang-baxter (x ∷ y ∷ z ∷ ws) i = z ∷ y ∷ x ∷ ws
    -- yang-baxter (x ∷ y ∷ sub t z ws j) i = bcat (λ ws _ → y ∷ ws) (sub t z) (x ∷ ws) j
    -- yang-baxter (x ∷ y ∷ yank z ws i j) k = yank z (y ∷ x ∷ ws) i j
    -- yang-baxter (x ∷ sub t x0 [] i) j = bcat-sq x t x0 [] i j
    -- yang-baxter (x ∷ sub t x0 (z ∷ ws) i) j = z ∷ sub t x0 (x ∷ ws) i
    -- yang-baxter (x ∷ sub t x0 (sub t1 x1 ws i) j) k = sub t1 x1 (sub t x0 (x ∷ ws) j) i
    -- yang-baxter (x ∷ sub t x0 (yank y ws i j) k) l = yank y (sub t x0 (x ∷ ws) k) i j
    -- yang-baxter (x ∷ yank y [] i j) k = {!!}
    -- yang-baxter (x ∷ yank y (z ∷ ws) i j) k = z ∷ yank y (x ∷ ws) i j
    -- yang-baxter (x ∷ yank y (sub t z ws i) j k) l = sub t z (yank y (x ∷ ws) j k) i
    -- yang-baxter (x ∷ yank y (yank z ws i j) k l) m = yank z (yank y (x ∷ ws) k l) i j
    -- yang-baxter (sub t x [] i) = rfl
    -- yang-baxter (sub t x (y ∷ []) i) j = {!bcat-sq ? ? ? ? j i!}
    -- yang-baxter (sub t x (y ∷ z ∷ ws) i) = rfl
    -- yang-baxter (sub t0 x0 (y ∷ sub t1 x1 ws i) j) = rfl
    -- yang-baxter (sub t x (y ∷ yank x₁ ws i₁ i₂) i) = rfl
    -- yang-baxter (sub t0 x0 (sub t1 x1 [] i) j) = {!!}
    -- yang-baxter (sub t0 x0 (sub t1 x1 (x ∷ ws) i) j) = rfl
    -- yang-baxter (sub t0 x0 (sub t1 x1 (sub t x ws i₁) i) j) = rfl
    -- yang-baxter (sub t0 x0 (sub t1 x1 (yank x ws i₁ i₂) i) j) = rfl
    -- yang-baxter (sub t x (yank y [] i j) k) = {!!}
    -- yang-baxter (sub t x (yank y (x₁ ∷ ws) i j) k) = rfl
    -- yang-baxter (sub t x (yank y (sub t₁ x₁ ws i₁) i j) k) = rfl
    -- yang-baxter (sub t x (yank y (yank x₁ ws i₁ i₂) i j) k) = rfl
    -- yang-baxter (yank x [] i i₁) = rfl
    -- yang-baxter (yank x (x₁ ∷ []) i i₁) = {!!}
    -- yang-baxter (yank x (x₁ ∷ x₂ ∷ ws) i i₁) = rfl
    -- yang-baxter (yank x (x₁ ∷ sub t x₂ ws i₂) i i₁) = rfl
    -- yang-baxter (yank x (x₁ ∷ yank x₂ ws i₂ i₃) i i₁) = rfl
    -- yang-baxter (yank x (sub t x₁ [] i₂) i i₁) = {!!}
    -- yang-baxter (yank x (sub t x₁ (x₂ ∷ ws) i₂) i i₁) = rfl
    -- yang-baxter (yank x (sub t x₁ (sub t₁ x₂ ws i₃) i₂) i i₁) = rfl
    -- yang-baxter (yank x (sub t x₁ (yank x₂ ws i₃ i₄) i₂) i i₁) = rfl
    -- yang-baxter (yank x (yank x₁ [] i₂ i₃) i i₁) = {!!}
    -- yang-baxter (yank x (yank x₁ (x₂ ∷ ws) i₂ i₃) i i₁) = rfl
    -- yang-baxter (yank x (yank x₁ (sub t x₂ ws i₄) i₂ i₃) i i₁) = rfl
    -- yang-baxter (yank x (yank x₁ (yank x₂ ws i₄ i₅) i₂ i₃) i i₁) = rfl



    -- data BView {u} {A : Type u} : BList A → Type u where
    --   nil : BView []
    --   cons : ∀ x ws → BView ws → BView (x ∷ ws)
    --   twist : ∀ x y ws → BView (x ∷ y ∷ ws) → BView (bflip (x ∷ y ∷ ws))
    --   untwist : ∀ x y ws → BView (x ∷ y ∷ ws) → BView (-bflip (x ∷ y ∷ ws))

    -- view : (ws : BList A) → BView ws
    -- view [] = nil
    -- view (x ∷ ws) = cons x ws (view ws)
    -- view (sub t x [] i) = {!!}
    -- view (sub t x (x₁ ∷ ws) i) = {!!}
    -- view (sub t x (sub t₁ x₁ ws i₁) i) = {!!}
    -- view (sub t x (yank x₁ ws i₁ i₂) i) = {!!}
    -- view (yank x ws i i₁) = {!!}

  -- bflip : BList A → BList A
  -- bflip [] = []
  -- bflip (x ∷ []) = x ∷ []
  -- bflip (x ∷ y ∷ ws) = y ∷ x ∷ ws
  -- bflip (x ∷ sub t x0 ws i) = hcomp (∂ i) λ where
  --   k (i = i0) → sub x0 t (x ∷ ws) k
  --   k (k = i0) → sub x0 t (x ∷ ws) i
  --   k (i = i1) → sub t x0 (x ∷ ws) k
  -- bflip (x ∷ yank x0 ws i j) = hcomp (∂ j ∨ i) λ where
  --   k (j = i0) → sub x0 x0 (x ∷ ws) k
  --   k (j = i1) → sub x0 x0 (x ∷ ws) k
  --   k (i = i1) → sub x0 x0 (x ∷ ws) k
  --   k (k = i0) → yank x0 (x ∷ ws) i j
  -- bflip (sub t x [] i) = sub t x [] i
  -- bflip (sub t x (y ∷ ws) i) = y ∷ sub t x ws i
  -- bflip (sub t0 x0 (sub t1 x1 ws i) j) = hcomp (∂ i ∨ j) λ where
  --   k (i = i0) → sub x1 t1 (sub t0 x0 ws j) k
  --   k (i = i1) → sub t1 x1 (sub t0 x0 ws j) k
  --   k (j = i1) → cat2.fill (sub x1 t1 (t0 ∷ ws)) (sub x1 t1 (t0 ∷ ws)) (sub t1 x1 (t0 ∷ ws)) i k
  --   k (k = i0) → sub x1 t1 (sub t0 x0 ws j) i
  -- bflip (sub t x (yank x₁ ws i₁ i₂) i) = {!hcomp (∂ i)!}
  -- bflip (yank x ws i i₁) = {!!}

  -- data BView {u} {A : Type u} : BList A → Type u where
  --   nil : BView []
  --   idn : ∀ x ws → BView ws → BView (x ∷ ws)
  --   pos1 : ∀ ws → BView ws → BView (bflip ws)
  --   pos2 : ∀ ws → BView ws → BView (bflip2 ws)

  b1 : ∀ x y z (xs : BList A) → x ∷ y ∷ z ∷ xs ≡ y ∷ x ∷ z ∷ xs
  b1 x y z xs = twist x y (z ∷ xs)
  {-# DISPLAY sub y x (sub x y (z ∷ ws) i) i = b1 x y z ws i #-}

  b2 : ∀ x y z (xs : BList A) → x ∷ y ∷ z ∷ xs ≡ x ∷ z ∷ y ∷ xs
  b2 x y z xs = ap (x ∷_) (twist y z xs)

  -- conj-eq : ∀ w x y z (zs : BList A)
  --         → ap (λ ws → w ∷ x ∷ ws) (twist y z zs) ∙ twist w x (z ∷ y ∷ zs)
  --         ≡ twist w x (y ∷ z ∷ zs) ∙ ap (λ ws → x ∷ w ∷ ws) (twist y z zs)
  -- conj-eq w x y z zs = cat.baxter
  --   (ap (λ ws → w ∷ x ∷ ws) (twist y z zs))
  --   (b1 w x y (z ∷ zs))
  --   (ap (λ ws → x ∷ w ∷ ws) (twist y z zs))
  --   (b1 w x z (y ∷ zs))
  --   (ap (λ ws → w ∷ x ∷ ws) (hsym (twist y z zs)) ∙ b1 w x y (z ∷ zs))
  --   α β where
  --   α : Square
  --         ((ap (λ ws → w ∷ x ∷ ws) (twist y z zs)))
  --         rfl
  --         (b1 w x y (z ∷ zs))
  --         (ap (λ ws → w ∷ x ∷ ws) (hsym (twist y z zs)) ∙ b1 w x y (z ∷ zs))
  --   α = {!!}

  --   β : Square
  --     rfl
  --     (ap (λ ws → w ∷ x ∷ ws) (hsym (twist y z zs)) ∙ b1 w x y (z ∷ zs))
  --     (ap (λ ws → x ∷ w ∷ ws) (twist y z zs))
  --     (b1 w x z (y ∷ zs))
  --   β i j = hcomp (imp i (i ∨ j)) λ where
  --     k (i = i0) → w ∷ x ∷ twist y z zs (j ∨ k)
  --     k (i = i1) → x ∷ w ∷ twist y z zs (j ∧ k)
  --     k (j = i1) → {!!}
  --     k (k = i0) → {!!}


  -- conj : ∀ w x y z (ws : BList A)
  --      → Square
  --        (ap (λ xs → w ∷ x ∷ xs) (twist y z ws))
  --        (twist w x (y ∷ z ∷ ws))
  --        (ap (λ xs → x ∷ w ∷ xs) (twist y z ws))
  --        (twist w x (z ∷ y ∷ ws))
  -- conj w x y z ws = {!cat.baxter!}

  -- slide : ∀ x y z (ws : BList A)
  --     → Square (b2 x y z ws)
  --              (b1 x y z ws)
  --              (b2 y x z ws ∙ b1 y z x ws)
  --              (b1 x z y ws ∙ b2 z x y ws)
  -- slide x y z ws =  {!!}

  -- twist : {A : Type u} → ∀ x y →
  -- twist = ?
  --twist : -- reidemeister move I
    -- conj : ∀ w x y z (ws : BList A)
    --      → Square
    --        (ap (λ xs → w ∷ x ∷ xs) (twist y z ws))
    --        (twist w x (y ∷ z ∷ ws))
    --        (ap (λ xs → x ∷ w ∷ xs) (twist y z ws))
    --        (twist w x (z ∷ y ∷ ws))

data BList {u} (A : Type u) : Type u where
  [] : BList A
  _∷_ : A → BList A → BList A
  twist : ∀ x y zs → x ∷ y ∷ zs ≡ y ∷ x ∷ zs -- positive twist
  yank : ∀ x xs → twist x x xs ≡ erfl (x ∷ x ∷ xs) -- reidemeister move I
  -- conj : ∀ w x y z (ws : BList A)
  --      → Square
  --        (ap (λ xs → w ∷ x ∷ xs) (twist y z ws))
  --        (twist w x (y ∷ z ∷ ws))
  --        (ap (λ xs → x ∷ w ∷ xs) (twist y z ws))
  --        (twist w x (z ∷ y ∷ ws))

# Denotations for braid group elements

> twist x y → bflip₁ x y
> twist y x → bflip₁ y x
> twist x y ∙ twist y x → bflip₁ x y ∙ bflip₁ y x ＝ bflip₁²
> hsym (twist y x) => -bflip₁ x y
> hsym (twist x y) => -bflip₁ y x
> hsym (twist x y) =>


infixr 6 _∷_

private variable
  u : Level
  A : Type u
  x y z : A
  xs ys : BList A

conj' : ∀ w x y z (ws : BList A)
     → Square
       (ap (λ xs → w ∷ x ∷ xs) (twist y z ws))
       (twist w x (y ∷ z ∷ ws))
       (ap (λ xs → x ∷ w ∷ xs) (twist y z ws))
       (twist w x (z ∷ y ∷ ws))
conj' w x y z ws i j = {!!} where
     s1 = ap (λ xs → w ∷ x ∷ xs) (twist y z ws)
     s2 = twist w x (y ∷ z ∷ ws)
     s3 = ap (λ xs → x ∷ w ∷ xs) (twist y z ws)
     s4 = twist w x (z ∷ y ∷ ws)

bcat : ∀ {x0 x1 t0 t1 xs zs}
     → (∀ (ys : BList A) → x0 ∷ x1 ∷ xs ≡ ys)
     → (∀ (ys : BList A) → ys ≡ t0 ∷ t1 ∷ zs)
     → ∀ (ws : BList A) → x0 ∷ x1 ∷ xs ≡ t0 ∷ t1 ∷ zs
bcat {A} p q ws i = q (p ws i) i

brefl : ∀ x (ws : BList A) → x ∷ ws ≡ x ∷ ws
brefl x ws _ = x ∷ ws
{-# INLINE brefl #-}

s1 : BList A → BList A
s1 [] = []
s1 (x ∷ []) = x ∷ []
s1 (x ∷ y ∷ ws) = y ∷ x ∷ ws
s1 (x ∷ twist y z ws i) =
  cat2 (twist x y (z ∷ ws)) (ap (x ∷_) (twist y z ws)) (twist x z (y ∷ ws)) i
s1 (x ∷ yank y ws i j) = {!!}
s1 (twist x y ws i) = twist y x ws i
s1 (yank x ws i j) = yank x ws i j

s2 : BList A → BList A
s2 [] = []
s2 (x ∷ ws) = x ∷ s1 ws
s2 (twist x y ws i) = {!!}
-- cat2 (twist z x (y ∷ ws)) (λ j → z ∷ twist x y ws j) (twist z y (x ∷ ws)) i
s2 (yank x ws i i₁) = {!!}

-- yang-baxter : (ws : BList A) → bflip2 (bflip (bflip2 ws)) ≡ bflip (bflip2 (bflip ws))
-- yang-baxter ws = ?

-- conj-center : ∀ x (xs : BList A) →
--               Square (twist x x (x ∷ x ∷ xs))
--               (ap (λ xs₁ → x ∷ x ∷ xs₁) (twist x x xs))
--               (twist x x (x ∷ x ∷ xs))
--               (ap (λ xs₁ → x ∷ x ∷ xs₁) (twist x x xs))
-- conj-center x xs i j = {!hcomp (∂ i ∨ j) ?!}

-- conj-refl : ∀ x xs → conj x x x x xs ≡ λ i j → {!!}
-- conj-refl w x y z = {!!}

W : ∀ x y z {ws : BList A} → x ∷ y ∷ z ∷ ws ≡ y ∷ z ∷ x ∷ ws
W x y z {ws} = twist x y (z ∷ ws) ∙ ap (y ∷_) (twist x z ws)

V : ∀ x y z {ws : BList A} → x ∷ y ∷ z ∷ ws ≡ z ∷ x ∷ y ∷ ws
V x y z {ws} = ap (x ∷_) (twist y z ws) ∙ twist x z (y ∷ ws)

b1 : ∀ x y z (xs : BList A) → x ∷ y ∷ z ∷ xs ≡ y ∷ x ∷ z ∷ xs
b1 x y z xs = twist x y (z ∷ xs)
{-# NOINLINE b1 #-}

b2 : ∀ x y z (xs : BList A) → x ∷ y ∷ z ∷ xs ≡ x ∷ z ∷ y ∷ xs
b2 x y z xs = ap (x ∷_) (twist y z xs)

untwist : ∀ x y (xs : BList A)
        → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
untwist x y xs = hsym (twist y x xs)
-- this is the negative 'untwisting' operation, establishing that we have oriented twists
-- and hence we are in a general braided (as opposed to symmetric) monoidal setting

invr : twist x y xs ∙ untwist y x xs ≡ rfl
invr {x} {y} {xs} = Lib.Path.Gpd.cat.invr (twist x y xs)

invl : untwist x y xs ∙ twist y x xs  ≡ rfl
invl {x} {y} {xs} = Lib.Path.Gpd.cat.invl (twist y x xs)
-- invr and invl establish reidemeister move II

-- -- Fake YBE, the real one comes as a result of slide
-- coh : ∀ x y z (ws : BList A)
--     → Square (b2 x y z ws) (b2 x y z ws ∙ b1 x z y ws) (b2 z x y ws) (b1 x z y ws ∙ b2 z x y ws)
-- coh x y z ws i j = hcomp (∂ i ∨ j) λ where
--   k (i = i0) → x ∷ twist y z ws (j ∨ ~ k)
--   k (i = i1) → z ∷ twist x y ws (j ∧ k)
--   k (j = i1) → Lib.Path.Gpd.cat.rfill (twist x z (y ∷ ws)) (ap (z ∷_) (twist x y ws)) i k
--   k (k = i0) → twist x z (y ∷ ws) i

-- coh2 : ∀ x y z (ws : BList A)
--     → Square (b1 x y z ws) (b1 x y z ws ∙ b2 y x z ws) (b1 y z x ws) (b2 y x z ws ∙ b1 y z x ws)
-- coh2 x y z ws i j = hcomp (∂ i ∨ j) λ where
--   k (i = i0) → b1 x y z ws (j ∨ ~ k)
--   k (i = i1) → b1 y z x ws (j ∧ k)
--   k (j = i1) → Lib.Path.Gpd.cat.fill (b2 y x z ws) (b1 y z x ws) i k
--   k (k = i0) → b2 y x z ws i

-- conj-eq  : ∀ w x y z (zs : BList A)
--          → ap (λ ws → w ∷ x ∷ ws) (twist y z zs) ∙ twist w x (z ∷ y ∷ zs)
--          ≡ twist w x (y ∷ z ∷ zs) ∙ ap (λ ws → x ∷ w ∷ ws) (twist y z zs)
-- conj-eq  w x y z zs = cat.commutes2
--   (ap (λ ws → w ∷ x ∷ ws) (twist y z zs))
--   (twist w x (z ∷ y ∷ zs))
--   (twist w x (y ∷ z ∷ zs))
--   (ap (λ ws → x ∷ w ∷ ws) (twist y z zs))
--   (conj w x y z zs)
slide : ∀ x y z (ws : BList A)
      → Square (b2 x y z ws)
               (b1 x y z ws)
               (b2 y x z ws ∙ b1 y z x ws)
               (b1 x z y ws ∙ b2 z x y ws)
slide x y z ws = squ1
    where
    module _ where
      a0 = x ∷ y ∷ z ∷ ws
      x0 = x ∷ z ∷ y ∷ ws
      x1 = z ∷ x ∷ y ∷ ws
      y0 = y ∷ x ∷ z ∷ ws
      y1 = y ∷ z ∷ x ∷ ws
      a1 = z ∷ y ∷ x ∷ ws
    module _ where
      a0→x0 : a0 ≡ x0
      a0→x0 = b2 x y z ws

      x0→x1 : x0 ≡ x1
      x0→x1 = b1 x z y ws

      x1→a1 : x1 ≡ a1
      x1→a1 = b2 z x y ws

    module _ where
      a0→y0 : a0 ≡ y0
      a0→y0 = b1 x y z ws

      y0→y1 : y0 ≡ y1
      y0→y1 = b2 y x z ws

      y1→a1 : y1 ≡ a1
      y1→a1 = b1 y z x ws

    module _ where
      w0 : x0 ≡ a1
      w0 = x0→x1 ∙ x1→a1

      w1 : y0 ≡ a1
      w1 = y0→y1 ∙ y1→a1

      w : x0 ≡ y0
      w = w0 ∙ hsym w1

      wf : Square w w0 rfl w1
      wf i j = Lib.Path.Gpd.cat.cone w0 w1 j i

    module _ where
      v0 : a0 ≡ x1
      v0 = a0→x0 ∙ x0→x1

      v1 : a0 ≡ y1
      v1 = a0→y0 ∙ y0→y1

      v : x1 ≡ y1
      v = hsym v0 ∙ v1

    module _ where

    module _ where
      q : x1 ≡ y1
      q = x1→a1 ∙ hsym y1→a1

      dest : a1 ≡ a1
      dest = hsym x1→a1 ∙ q ∙ y1→a1

    y1→y0 : y1 ≡ y0
    y1→y0 = b2 y z x ws

    y0→a0 : y0 ≡ a0
    y0→a0 = b1 y x z ws

    a1→x1 : a1 ≡ x1
    a1→x1 = b2 z y x ws

    x1→x0 : x1 ≡ x0
    x1→x0 = b1 z x y ws

    n : a1 ≡ x0
    n = a1→x1 ∙ x1→x0

    module _ where
      a1→y1 : a1 ≡ y1
      a1→y1 = b1 z y x ws

      x0→a0 : x0 ≡ a0
      x0→a0 = b2 x z y ws

    module _ where
      vf : Square (erfl a0) v0 v v1
      vf i j = Lib.Path.Gpd.cat.fan v0 v1 j i

      qf : Square x1→a1 q y1→a1 rfl
      qf = Lib.Path.Gpd.cat.cone x1→a1 y1→a1

    c0 : x0 ≡ y0
    c0 = hsym a0→x0 ∙ a0→y0

    module c0 where
      -- a0→x0 : a0 ≡ x0
      -- a0→x0 = b2 x y z ws

      -- a0→y0 : a0 ≡ y0
      -- a0→y0 = b1 x y z ws

      pf : Square a0→x0 (erfl a0) a0→y0 c0
      pf = Lib.Path.Gpd.cat.fan a0→x0 a0→y0

      -- x0→x1 : x0 ≡ x1
      -- x0→x1 = b1 x z y ws

      -- x1→a1 : x1 ≡ a1
      -- x1→a1 = b2 z x y ws

    module c1 where
      -- y0→y1 : y0 ≡ y1
      -- y0→y1 = b2 y x z ws

    module c2 where

      -- y1→a1 : y1 ≡ a1
      -- y1→a1 = b1 y z x ws



    module x0→y1 where
      p0 : x0 ≡ y1
      p0 = hsym a0→x0 ∙ a0→y0 ∙ y0→y1

      p1 : x0 ≡ y1
      p1 = x0→x1 ∙ x1→a1 ∙ hsym y1→a1

      unit : x0 ≡ x0
      unit = p0 ∙ hsym p1

      counit : y1 ≡ y1
      counit = hsym p0 ∙ p1

      unit-sq : Square p0 unit p1 rfl
      unit-sq = Lib.Path.Gpd.cat.cone p0 p1

      counit-sq : Square p0 rfl p1 counit
      counit-sq = Lib.Path.Gpd.cat.fan p0 p1

      e0 : p0 ≡ p1
      e0 i j = hcomp (∂ j ∨ ~ i) λ where
        k (i = i0) → unit-sq (~ k) j
        k (j = i0) → {!!} -- (hsym a0→x0 ∙ a0→y0 ∙ y0→y1) ∙ (hsym x0→x1 ∙ x1→a1 ∙ hsym y1→a1) ⌞ ? ⌟ hsym x0→x1 => rfl
        k (j = i1) → y1
        k (k = i0) → {!p1!}
        

      fill : Square unit p0 counit p1
      fill i j = hcomp (∂ i ∨ ∂ j) λ where
        k (j = i0) → conn (hsym p0) p0 i k
        k (j = i1) → conn (hsym p1) p1 i k
        k (i = i0) → unit-sq j (~ k)
        k (i = i1) → counit-sq j k
        k (k = i0) → {!!}


    -- u0 : Square rfl x0→y1 y1→y0 (hsym a0→x0 ∙ a0→y0)
    -- u0 i j = hcomp (∂ i ∨ j) λ where
    --   k (i = i0) → {!!}
    --   k (i = i1) → {!!}
    --   k (j = i1) → {!!}
    --  k (k = i0) → {!!}




    -- https://q.uiver.app/#q=WzAsMjQsWzUsMCwibDEiXSxbNCw3LCJ2MCJdLFs2LDUsImwzIl0sWzgsMywidzAiXSxbMTgsMiwicjEiXSxbMTMsMTEsInIzIl0sWzEwLDksInYxIl0sWzMsNSwibTAqbTEiXSxbMCw1LCJtMCJdLFsxLDEsIc'b'xKmwxIl0sWzEsMTIsIc'b'yKc'b'wIl0sWzAsOSwibTIiXSxbMywxMCwibTEiXSxbMTgsMTEsInIzKm4wIl0sWzE5LDE3LCJuMSJdLFsxMCwxNCwibjAqbjEiXSxbMTYsMTMsIm4xKm4yIl0sWzE5LDEwLCJuMipyMSJdLFsxNCwxNCwibjIiXSxbMTQsMTIsIm4wIl0sWzEzLDQsIncxIl0sWzgsNywicmZsKGEpIl0sWzExLDIsInciXSxbOCwxMywidiJdLFs2LDQsInh5ejEoaTApKGspIiwyXSxbNiw1LCJ4eXoxKGkxKShrKSJdLFswLDMsInh5ejAoaykoaTEpIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIx1→x09fV0sWzIsMywieHl6MChrKShpMSkiLDJdLFsxLDAsInh5ejAoaTApKGspIl0sWzEsMiwieHl6MChpMSkoaykiLDJdLFswLDksInl6eChrKShpMSkiXSxbOCw5LCJ5engwKGspKGkxKSIsMl0sWzcsOCwieXp4MChpMCkoaykiLDJdLFs3LDAsInl6eDAoaTEpKGspIiwyXSxbMTAsMTEsInp5eDEoaTApKGspIiwyXSxbMTAsMTIsInp5eDEoaTApKGspIl0sWzExLDcsInp5eDEoaykoaTEpIiwyXSxbMTIsNywienl4MShrKShpMSkiLDJdLFsxMyw1LCJ5eHoxKGkwKShrKSJdLFsxMywxNCwieXh6MShpMSkoaykiLDJdLFs1LDE1LCJ5eHoxKGspKGkxKSIsMl0sWzE0LDE1LCJ5eHoxKGspKGkxKSIsMV0sWzE2LDE0LCJ6eHkxKGkwKShrKSIsMV0sWzE0LDE3LCJ6eHkxKGspKGkxKSIsMV0sWzQsMTcsInp4eTEoaykoaTEpIiwxXSxbMTYsNCwienh5MShpMSkoaykiLDFdLFsxNSwxOSwieHl6MChpMCkoaykiLDFdLFsxNSwxOCwieHl6MChpMSkoaykiLDFdLFsxOSwxNiwieHl6MChrKShpMSkiLDFdLFsxOCwxNiwieHl6MChrKShpMSkiLDFdLFs0LDAsIiIsMix7InA1→X1eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyMSwyMCwid2YoaykoaTEpIiwyXSxbMywyMSwid2YoaTEpKGspIiwyXSxbMywyMiwid2YoaTApKGspIiwyXSxbMjIsMjAsIndmKGspKGkxKSIsMl0sWzIzLDYsInZmKGspKGkxKSJdLFsxLDIxLCJ2ZihpMCkoaykiXSxbMSwyMywidmYoaTEpKGspIiwxXSxbMjEsNiwidmYoaykoaTEpIiwxXSxbNCwyMCwieHl6MShrKShpMSkiLDJdLFs1LDIwLCJ4eXoxKGspKGkxKSJdXQ==
    v0=>w0 : Square a0→x0 v0 x1→a1 w0
    v0=>w0 = coh x y z ws

    yzx0 : Square y1→y0 (y1→y0 ∙ y0→a0) a0→x0 (y0→a0 ∙ a0→x0)
    yzx0 = coh y z x ws

    zyx1 : Square a1→y1 (a1→y1 ∙ y1→y0) y0→a0 (y1→y0 ∙ y0→a0)
    zyx1 = coh2 z y x ws

    zyx0 : Square a1→x1 (a1→x1 ∙ x1→x0) x0→a0 (x1→x0 ∙ x0→a0)
    zyx0 = coh z y x ws

    yzx1 : Square y1→a1 (y1→a1 ∙ a1→x1) x1→x0 (a1→x1 ∙ x1→x0)
    yzx1 = coh2 y z x ws

    xyz1 : Square a0→y0 v1 y1→a1 w1
    xyz1 = coh2 x y z ws

    zxy0 : Square x1→a1 (x1→a1 ∙ a1→y1) y1→y0 (a1→y1 ∙ y1→y0)
    zxy0 = coh z x y ws

    zxy1 : Square x1→x0 (x1→x0 ∙ x0→a0) a0→y0 (x0→a0 ∙ a0→y0)
    zxy1 = coh2 z x y ws

    xzy0 : Square x0→a0 (x0→a0 ∙ a0→y0) y0→y1 (a0→y0 ∙ y0→y1)
    xzy0 = coh x z y ws

    xzy1 : Square x0→x1 (x0→x1 ∙ x1→a1) a1→y1 (x1→a1 ∙ a1→y1)
    xzy1 = coh2 x z y ws

    -- z0 : Square v x1→a1 (a1→x1 ∙ x1→x0) {!!}
    -- z0 = {!!}

    -- esq0 : Square (hsym a0→y0 ∙ v0) (hsym w) x0→x1 (erfl x1)
    -- esq0 = {!!}

    -- esq-lm  : Square p rfl x0→x1 (y0→a0 ∙ a0→x0 ∙ x0→x1)
    -- esq-lm = {!!}

    esq : Square c0 rfl x0→x1 (hsym a0→y0 ∙ a0→x0 ∙ x0→x1)
    esq i j = hcomp (∂ j ∨ ∂ i) λ where
      k (i = i0) → {!!}
      k (i = i1) → {!!}
      k (j = i0) → x ∷ z ∷ y ∷ ws
      k (j = i1) → {!!}
      k (k = i0) → x ∷ z ∷ y ∷ ws
    --Lib.Path.Gpd.cat.paste (hsym a0→y0 ∙ v0) x0→x1 (hsym w) esq0 (ap hsym hmm)

    rsq : Square y0→y1 (hsym a0→y0 ∙ v0) (x1→a1 ∙ hsym y1→a1) rfl
    rsq = {!!}

    -- pst : Square x0→x1 p y0→y1 (x1→a1 ∙ hsym y1→a1)
    -- pst = Lib.Path.Gpd.cat.paste (x1→a1 ∙ hsym y1→a1) y0→y1 (hsym v0 ∙ a0→y0) {!λ i j → rsq j i!} {!!}

    ψ : Square x0→x1 c0 y0→y1 (x1→a1 ∙ hsym y1→a1)
    ψ = Lib.Path.Gpd.paste-alt y0→y1 (x1→a1 ∙ hsym y1→a1) rsq esq

    -- k=i0 : Square a1→y1 (a1→x1 ∙ x1→x0) x0→a0 (y1→y0 ∙ y0→a0)
    -- k=i0 = {!!}

    -- j=i0 : Square (hsym (x0→x1 ∙ x1→a1)) (a1→x1 ∙ x1→x0) (x0→a0 ∙ a0→y0) (hsym a0→x0 ∙ a0→y0)
    -- j=i0 = {!!}

    -- j=i1 : Square (hsym (x1→a1 ∙ a1→y1)) (y1→y0 ∙ y0→a0) (a0→y0 ∙ y0→y1) (x1→a1 ∙ hsym y1→a1)
    -- j=i1 = {!!}

    -- j1 : Square x0→x1 p y0→y1 (x1→a1 ∙ hsym y1→a1)
    -- j1 i j = hcomp (∂ i ∨ ∂ j) λ where
    --   k (i = i0) → xzy1 (~ k) j
    --   k (i = i1) → xzy0 k j
    --   k (j = i0) → j=i0 i k
    --   k (j = i1) → j=i1 i k
    --   k (k = i0) → k=i0 i j

    φ : Square v0 rfl v1 q
    φ i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → Lib.Path.Gpd.cat.fill a0→x0 x0→x1 j k
      k (i = i1) → Lib.Path.Gpd.cat.fill a0→y0 y0→y1 j k
      k (j = i0) → Lib.Path.Gpd.cat.cone (hsym a0→x0) (hsym a0→y0) i k
      k (j = i1) → ψ i k
      k (k = i0) → c0 i

    sq : Square w0 (hsym a0→x0 ∙ a0→y0) w1 rfl
    sq i j = hcomp (∂ i ∨ ∂ j) λ where
       k (i = i0) → v0=>w0 j k
       k (i = i1) → xyz1 j k
       k (j = i0) → Lib.Path.Gpd.cat.fill (hsym a0→x0) a0→y0 i k
       k (j = i1) → qf i k
       k (k = i0) → φ i j

    squ1 : Square a0→x0 a0→y0 w1 w0
    squ1 i j = Lib.Path.Gpd.paste-alt w0 w1 sq c0.pf j i
ybe : ∀ x y z (ws : BList A)
    → b2 x y z ws ∙ b1 x z y ws ∙ b2 z x y ws
    ≡ b1 x y z ws ∙ b2 y x z ws ∙ b1 y z x ws
ybe x y z ws = cat.baxter
  (b2 x y z ws)
  (b1 x y z ws)
  (b2 y x z ws ∙ twist y z (x ∷ ws))
  (b1 x z y ws ∙ b2 z x y ws)
  (b2 x z y ws ∙ b1 x y z ws)
  α {!!} where
  α : Square (b2 x y z ws) rfl (b1 x y z ws) (b2 x z y ws ∙ b1 x y z ws)
  lem : Square (b2 x y z ws) rfl (b1 x y z ws) (b2 x z y ws ∙ b1 x y z ws)
  lem = {!!}
  α i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i1) → b1 x y z ws (j ∧ k)
    k (j = i0) → b2 x z y ws (i ∨ k)
    k (k = i0) → b2 x z y ws (i ∨ j)
    k (i = i0) → conn (b2 x z y ws) (b2 x y z ws) j k
    k (j = i1) → {!!}

  sq0 : Square (b2 x y z ws) rfl (b1 x y z ws) (hsym (b2 x y z ws) ∙ b1 x y z ws)
  sq0 = cat.fan (b2 x y z ws) (b1 x y z ws)
-- Lib.Path.Gpd.cat.commutes2 (b2 x y z ws) (λ i → (b1 x z y ws ∙ b2 z x y ws) i) (λ i → b1 x y z ws i) (b2 y x z ws ∙ b1 y z x ws) (slide x y z ws)

yang-baxter : ∀ (x y z : A) (ws : BList A)
           → twist x y (z ∷ ws) ∙ ap (y ∷_) (twist x z ws) ∙ twist y z (x ∷ ws)
           ≡ ap (x ∷_) (twist y z ws) ∙ twist x z (y ∷ ws) ∙ ap (z ∷_) (twist x y ws)
yang-baxter x y z ws i j = hcomp (∂ j ∨ i) λ where
  k (j = i0) → {!!}
  k (k = i0) → {!Lib.Path.Gpd.cat.fill {!!} {!!} i j!} -- sq-neutral (by0→y1 x y z ws) (ba0→y0 y x z ws) i j
  k (j = i1) → z ∷ y ∷ x ∷ ws  -- Lib.Path.Gpd.cat.rfill (ba0→y0 y x z ws) (by0→y1 y z x ws) k (~ i ∨ k)
  k (i = i1) → {!!} -- Lib.Path.Gpd.cat.fill p0 p1 j k
     -- Lib.Path.Gpd.cat.rfill (ba0→y0 x y z ws) p0 j k
      where
    p0 = ap (_∷_ x) (twist y z ws)
    p1 = (twist x z (y ∷ ws) ∙ ap (_∷_ z) (twist x y ws))

    q0 = twist x y (z ∷ ws)
    q1 = (ap (_∷_ y) (twist x z ws) ∙ twist y z (x ∷ ws))

    w : Square q1 (twist y x (z ∷ ws) ∙ ap (x ∷_) (twist y z ws)) p1 rfl
    w = {!!}
    _ : Square (λ j₁ → _∙_.fill p0 p1 j₁ i0) (λ i₁ → _∙_.fill p0 p1 i0 i₁) (λ j₁ → _∙_.fill p0 p1 j₁ i1) λ i₁ → _∙_.fill p0 p1 i1 i₁
    _ = λ i j → Lib.Path.Gpd.cat.fill p0 p1 j i

-- slide : ∀ x y z (xs : BList A)
--       → ba0→y0 x y z xs ∙ by0→y1 x z y xs ∙ ba0→y0 z x y xs
--       ≡ by0→y1 x y z xs ∙ ba0→y0 y x z xs ∙ by0→y1 y z x xs
-- slide x y z xs i j = hcomp (∂ j ∨ i) λ where
--   k (j = i0) → hsym (twist x y (z ∷ xs)) (~ i ∨ k)
--   k (j = i1) → w2 (k ∨ ~ i)
--   k (i = i1) → Lib.Path.Gpd.fill (by0→y1 x y z xs) w2 j k
--   k (k = i0) → hcomp (∂ j ∨ i) λ where
--     k (j = i0) → {!!}
--     k (j = i1) → {!Lib.Path.Gpd.fill (by0→y1 x z y xs) (ba0→y0 z x y xs) k!}
--     k (i = i1) → {!w0 !}
--     k (k = i0) → x ∷ twist y z xs (i ∨ j)
--      where
--   w0 = by0→y1 x z y xs ∙ ba0→y0 z x y xs
--   w1 = by0→y1 x y z xs ∙ ba0→y0 y x z xs
--   w2 = ba0→y0 y x z xs ∙ by0→y1 y z x xs

  -- w : Square w0 (ap (x ∷_) (twist z y)) w1 (twist z y)
  -- w = {!!}

--   α : s1 ∙ untwist y x xs ≡ a0
--   α = ap (_∙ untwist y x xs) (hsym p0)
--     ∙ hsym (Lib.Path.Gpd.assoc a0 (twist x y xs) (untwist y x xs))
--     ∙ ap (a0 ∙_) (invr x y xs)
--     ∙ Lib.Path.Gpd.unitr a0

--   δ : (s1 ∙ untwist y x xs) ∙ twist x y xs ≡ s1
--   δ = hsym (Lib.Path.Gpd.assoc s1 (untwist y x xs) (twist x y xs))
--      ∙ ap (s1 ∙_) (invl x y xs)
--      ∙ Lib.Path.Gpd.unitr s1

--   s0 : xs ≡ y ∷ x ∷ xs
--   s0 = α i ∙ twist x y xs

--   w0 : Square (hsym (α i)) rfl (twist x y xs) s0
--   w0 = Lib.Path.Gpd.fill (α i) (twist x y xs)

--   w1 : Square (hsym a0) rfl (twist x y xs) s1
--   w1 = {!!}

  -- sq : Square s0 rfl s1 rfl
  -- sq j k = hcomp (i ∨ ∂ j ∨ ∂ k) λ where
  --   m (i = i1) → {!!}
  --   m (j = i0) → {!Lib.Path.Gpd.fill ? ? k (~ i ∧ m)!}
  --   m (j = i1) → {!s1 !}
  --   m (k = i0) → s0 (i ∧ j ∧ ~ m)
  --   m (k = i1) → {!!}
  --   m (m = i0) → {!!}


sing : A → BList A
sing a = a ∷ []

-- slide : (x y z : A) (ks : BList A) → ba0→y0 x y z ks ∙ by0→y1⁻ z x y ks ≡ ba0→y0⁻ x z y ks ∙ by0→y1 x z y ks
-- slide x y z ks i j = hcomp (∂ j ∨ ~ i) λ where
--   k (j = i0) → hsym br₁ (i ∨ k)
--   k (j = i1) → z ∷ x ∷ y ∷ ks
--   k (i = i0) → Lib.Path.Gpd.rfill br₁ br₂⁻ j k
--   k (k = i0) → ρ i j where
--     br₁ = ba0→y0 x y z ks
--     br₂ = by0→y1 x z y ks
--     br₁⁻ = ba0→y0⁻ x z y ks
--     br₂⁻ = by0→y1⁻ z x y ks

--     w1 : Square br₂⁻ br₂⁻ {!!} {!!}
--     w1 = {!!}

--     φ : Square (by0→y1⁻ z x y ks) (ba0→y0⁻ x y z ks) (ba0→y0⁻ x z y ks) (by0→y1⁻ x z y ks)
--     φ i j = hcomp (∂ i ∨ ∂ j) λ where
--         k (i = i0) → {!!}
--         k (i = i1) → x ∷ untwist y z ks (j ∧ k)
--         k (j = i0) → x ∷ untwist z y ks (i ∨ ~ k)
--         k (j = i1) → {!!}
--         k (k = i0) → x ∷ y ∷ z ∷ ks

--     ρ : Square br₂⁻ (hsym br₁) (br₁⁻ br₂) rfl
--     ρ i j = hcomp (∂ j ∨ ~ i) λ where
--       k (j = i0) → x ∷ twist y z ks (~ i)
--       k (i = i0) → twist z x (y ∷ ks) (~ j)
--       k (j = i1) → twist x z (y ∷ ks) (k ∨ ~ i)
--       k (k = i0) → φ i j

-- helper for ap
idn : {a : A} → BList A → BList A
idn {a} = cons a

-- ybe : (x y z : A) (ks : BList A)
--     → untwist y x (z ∷ ks) ∙ ap (cons y) (twist x z ks) ∙ untwist z y (x ∷ ks)
--     ≡ ap (cons x) (twist y z ks) ∙ untwist z x (y ∷ ks) ∙ ap (cons z) (twist x y ks)
-- ybe x y z ks i j = hcomp (∂ j ∨ ~ i) λ where
--   k (j = i0) → x ∷ y ∷ z ∷ ks
--   k (j = i1) → z ∷ y ∷ x ∷ ks
--   k (i = i0) → {!!}
--   k (k = i0) → conn-cat (ap (cons x) (twist y z ks)) u2 (~ i) j  where

--   test : {!!}
--   test = {!!}

--   a : x ∷ y ∷ z ∷ ks ≡ y ∷ x ∷ z ∷ ks
--   a = untwist y x (z ∷ ks)

--   b : z ∷ x ∷ y ∷ ks ≡ z ∷ y ∷ x ∷ ks
--   b = ap (z ∷_) (twist x y ks)

--   u2 : x ∷ z ∷ y ∷ ks ≡ z ∷ y ∷ x ∷ ks
--   u2 = untwist z x (y ∷ ks) ∙ ap (z ∷_) (twist x y ks)

--   w1 : y ∷ x ∷ z ∷ ks ≡ z ∷ y ∷ x ∷ ks
--   w1 = ap (y ∷_) (twist x z ks) ∙ untwist z y (x ∷ ks)

--   w2 : x ∷ y ∷ z ∷ ks ≡ z ∷ x ∷ y ∷ ks
--   w2 = ap (x ∷_) (twist y z ks) ∙ untwist z x (y ∷ ks)

--   w : Square w1 (twist y x (z ∷ ks)) w2 (ap (z ∷_) (twist y x ks))
--   w = {!!}

yang-baxter : ∀ (x y z : A) (xs : BList A)
           → twist x y (z ∷ xs) ∙ ap (cons y) (twist x z xs) ∙ twist y z (x ∷ xs)
           ≡ ap (x ∷_) (twist y z xs) ∙ twist x z (y ∷ xs) ∙ ap (z ∷_) (twist x y xs)
yang-baxter x y z xs i j = yb i j where
  a0→x0 : x ∷ y ∷ z ∷ xs ≡ y ∷ x ∷ z ∷ xs
  a0→x0 = twist x y (z ∷ xs)

  x0→x1 : y ∷ x ∷ z ∷ xs ≡ y ∷ z ∷ x ∷ xs
  x0→x1 = ap (y ∷_) (twist x z xs)

  x1→a1 : y ∷ z ∷ x ∷ xs ≡ z ∷ y ∷ x ∷ xs
  x1→a1 = twist y z (x ∷ xs)

  a0→y0 : x ∷ y ∷ z ∷ xs ≡ x ∷ z ∷ y ∷ xs
  a0→y0 = ap (x ∷_) (twist y z xs)

  y0→y1 : x ∷ z ∷ y ∷ xs ≡ z ∷ x ∷ y ∷ xs
  y0→y1 = twist x z (y ∷ xs)

  y1→a1 : z ∷ x ∷ y ∷ xs ≡ z ∷ y ∷ x ∷ xs
  y1→a1 = ap (z ∷_) (twist x y xs)

  -- s1 : Square (untwist x y (z ∷ xs)) (twist y x (z ∷ xs) ∙ a0→y0) rfl a0→y0
  -- s1 i j = hcomp (∂ i ∨ j) λ where
  --   k (j = i1) → x ∷ twist y z xs i
  --   k (i = i1) → x ∷ z ∷ y ∷ xs
  --   k (k = i0) → sq-neutral (twist y x (z ∷ xs)) a0→y0 i (i ∨ j)
  --   k (i = i0) → hcomp (∂ j ∨ ∂ k) λ where
  --     l (j = i0) → twist x y (z ∷ xs) l
  --     l (j = i1) → x ∷ y ∷ z ∷ xs
  --     l (k = i1) → twist x y (z ∷ xs) (~ j ∧ l)
  --     l (l = i0) → x ∷ y ∷ z ∷ xs
  --     l (k = i0) →

  w0 : Square x0→x1 (twist y x (z ∷ xs)) (a0→y0 ∙ y0→y1 ∙ y1→a1) (twist y z (x ∷ xs))
  w0 = {!!}

  w1 : Square a0→y0  (a0→y0 ∙ y0→y1 ∙ y1→a1) rfl (conn y0→y1 y1→a1)
  w1 = {!!}

  -- s2 : Square x0→x1 (twist y x (z ∷ xs) ∙ a0→y0) (conn y0→y1 y1→a1) x1→a1
  -- s2 i j = hcomp (∂ i ∨ j) λ where
  --   k (i = i0) → y ∷ twist x z xs j
  --   k (j = i1) → invol y z (x ∷ xs) k (~ i)
  --   k (i = i1) → conn y0→y1 y1→a1 j
  --   k (k = i0) → hcomp (∂ i ∨ j) λ where
  --     k (i = i0) → x0→x1 j
  --     k (j = i1) → invol z y (x ∷ xs) k i
  --     k (k = i0) → w0 i j
  --     k (i = i1) → w1 j k

  -- s3 : Square (a0→x0 ∙ x0→x1) a0→y0 (y0→y1 ∙ y1→a1) x1→a1
  -- s3 i j = hcomp (∂ j ∨ ~ i) λ where
  --   k (j = i0) → s1 i k
  --   k (i = i0) → Lib.Path.Gpd.rfill a0→x0 x0→x1 j k
  --   k (j = i1) → x1→a1 i
  --   k (k = i0) → s2 i j


  -- b : Square (hsym a0→x0) x0→x1 x1→a1 (conn a0→y0 (y0→y1 ∙ y1→a1))
  -- b i j = hcomp (∂ i ∨ ~ j) λ where
  --   k (i = i0) → a0→x0 (~ j ∧ k)
  --   k (j = i0) → Lib.Path.Gpd.sfill a0→x0 x0→x1 i k
  --   k (i = i1) → s3 j k
  --   k (k = i0) → a0→y0 (i ∧ j)

  -- ρ : Square (untwist x y (z ∷ xs)) rfl (x0→x1 ∙ x1→a1) (a0→y0 ∙ (y0→y1 ∙ y1→a1))
  -- ρ i j = hcomp (∂ i ∨ ~ j) λ where
  --   k (i = i0) → a0→x0 (~ j)
  --   k (j = i0) → x0→x1 (i ∧ ~ k)
  --   k (i = i1) → Lib.Path.Gpd.rfill x0→x1 x1→a1 j k
  --   k (k = i0) → b i j

  -- yb : a0→x0 ∙ x0→x1 ∙ x1→a1 ≡ a0→y0 ∙ y0→y1 ∙ y1→a1
  -- yb i j = hcomp (∂ j ∨ i) λ where
  --   k (j = i0) → twist x y (z ∷ xs) (i ∧ ~ k)
  --   k (j = i1) → (x0→x1 ∙ x1→a1) (k ∨ ~ i)
  --   k (k = i0) → conn.fill a0→x0 (x0→x1 ∙ x1→a1) j (~ i)
  --   k (i = i1) → ρ j k

  -- a0 : Square rfl (a0→y0 ∙ y0→y1) (untwist x z (y ∷ xs)) (ap (x ∷_) (twist y z xs))
  -- a0 = {!!}

  -- a1 : Square a0→y0 {!!} rfl (y0→y1 ∙ y1→a1)
  -- a1 = {!!}

  -- y0→a0 : Square rfl (a0→x0 ∙ x0→x1) (twist y z (x ∷ xs)) (a0→y0 ∙ (y0→y1 ∙ y1→a1))
  -- y0→a0 i j = hcomp (∂ i ∨ j) λ where
  --   k (i = i0) → x ∷ y ∷ z ∷ xs
  --   k (j = i1) → Lib.Path.Gpd.lfill a0→y0 (y0→y1 ∙ y1→a1) i k
  --   k (i = i1) → {!!}
  --   k (k = i0) → {!!}

  -- left : a0→x0 ≡ ap (x ∷_) (twist y z xs) ∙ y0→y1 ∙ {!y0→y1!}
  -- left = {!!}


  -- eq eqalt : a0→x0 ∙ x0→x1 ∙ x1→a1 ≡ a0→y0 ∙ y0→y1 ∙ y1→a1
  -- eq i j = hfill (∂ j ∨ i) i λ where
  --   k (j = i0) → x ∷ y ∷ z ∷ xs
  --   k (j = i1) → z ∷ y ∷ x ∷ xs
  --   k (k = i0) → coh a0→x0 (x0→x1 ∙ x1→a1) (~ j) j (~ i ∧ j)
  --   k (i = i1) → hcomp (∂ j ∨ k) λ where
  --     l (j = i0) → x ∷ y ∷ z ∷ xs
  --     l (j = i1) → rfill x0→x1 x1→a1 l (~ k)
  --     l (l = i0) → Lib.Path.Gpd.lfill a0→x0 x0→x1 j k
  --     l (k = i1) → y0→a0 j l

  -- eqalt i j = {!Lib.Path.Gpd.cat ? ? i j!}
`

-- ind : (P : BList A → Type v)
--     → P []
--     → (s : ∀ x xs → P xs → P (x ∷ xs))
--     → (∀ x y acc → (p : P acc)
--                 → s x (y ∷ acc) (s y acc p) ≡ s y (x ∷ acc) (s x acc p)
--                 :: ∂.line P (twist x y acc))
--     → ∀ xs → P xs
-- ind P b s q [] = b
-- ind P b s q (x ∷ xs) = s x xs (ind P b s q xs)
-- ind P b s q (twist x y xs i) = q x y xs (ind P b s q xs) i

-- len : BList A → Nat
-- len [] = 0
-- len (x ∷ xs) = S (len xs)
-- len (twist x y xs i) = S (S (len xs))

-- cat : BList A → BList A → BList A
-- cat [] bs = bs
-- cat (x ∷ as) bs = x ∷ (cat as bs)
-- cat (twist x y xs i) = λ z → twist x y (cat xs z) i

-- map : {B : Type v}
--     → (f : A → B)
--     → BList A → BList B
-- map f [] = []
-- map f (x ∷ xs) = f x ∷ map f xs
-- map f (twist x y xs i) = twist (f x) (f y) (map f xs) i

-- foldr : {B : Type v}
--       → (f : A → B → B)
--       → (∀ x y z → f x (f y z) ≡ f y (f x z))
--       → B → BList A → B
-- foldr {B} f comm b = ind (λ _ → B) b (λ x xs rec → f x rec) (λ x y acc rec → comm x y rec)

-- reverse : BList A → BList A
-- reverse xs = {!!}
-- ind : (P : BList A → Type v)
--     → P []
--     → (s : ∀ x xs → P xs → P (x ∷ xs))
--     → (∀ {w x y z xs ys} (q : w ∷ x ∷ xs ≡ y ∷ z ∷ ys) (a : P xs) (b : P ys)
--         → s w (x ∷ xs) (s x xs a) ≡ s z (y ∷ ys) (s y ys b)
--         :: λ i → P (braid w x xs {y} {z} {ys} q i))
--     → ∀ xs → P xs
-- ind P b s q [] = b
-- ind P b s q (x ∷ xs) = s x xs (ind P b s q xs)
-- ind P b s q (braid w x xs {y} {z} {ys} p i) = q p (ind P b s q xs) (ind P b s q ys) i
-- ind P b s q (yank x xs i i₁) = {!!}
