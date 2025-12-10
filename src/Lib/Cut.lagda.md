```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Cut where

open import Lib.Type

record Cut {u v w z}
  {A : Type u}
  (B : A → Type v) -- Γ ⊢ B , Δ
  (C : A → Type w) -- Π , B ⊢ Λ
  (D : ∀ x → B x → Type z) -- Π , Γ ⊢ Λ , Δ
  : Typeω
  where
  constructor #cut
  infixr 40 seq _∘_
  field
    seq : ∀ {x} (b : B x) (c : C x) → D x b
  {-# INLINE seq #-}

  _∘_ : ∀ {x} (c : C x) (b : B x) → D x b
  c ∘ b = seq b c
  {-# INLINE _∘_ #-}

  cut-syntax : ∀ x → (b : B x) (c : C x) → D x b
  cut-syntax x = seq
  {-# INLINE cut-syntax #-}
  syntax cut-syntax x a b = x ⟩ a ∣ b
{-# INLINE #cut #-}

open Cut ⦃ ... ⦄ hiding (seq) public

_∙_ : ∀ {u v w z} {A : Type u} {B : A → Type v} {C : A → Type w}
    → {D : ∀ x → B x → Type z} ⦃ cut : Cut B C D ⦄
    → ∀ {x} (b : B x) (c : C x) → D x b
_∙_ ⦃ cut ⦄ = Cut.seq cut
infixr 40 _∙_

{-# DISPLAY Cut.seq _ f g = f ∙ g #-}
{-# DISPLAY Cut._∘_ _ f g = _∘_ f g #-}
{-# DISPLAY cut-syntax _ p q = p ∙ q #-}

-- different operator; use it for 2-cell composition
record Cut-alt {u v w z}
  {A : Type u}
  (B : A → Type v) -- Γ ⊢ B , Δ
  (C : A → Type w) -- Π , B ⊢ Λ
  (D : ∀ x → B x → Type z) -- Π , Γ ⊢ Λ , Δ
  : Typeω
  where
  constructor #cut-alt
  field
    seq : ∀ {x} (b : B x) (c : C x) → D x b
  {-# INLINE seq #-}

{-# INLINE #cut-alt #-}

_⨾_ : ∀ {u v w z} {A : Type u} {B : A → Type v} {C : A → Type w}
    → {D : ∀ x → B x → Type z} ⦃ cut : Cut-alt B C D ⦄
    → ∀ {x} (b : B x) (c : C x) → D x b
_⨾_ ⦃ cut ⦄ = Cut-alt.seq cut 
infixr 40 _⨾_

{-# DISPLAY Cut.seq _ f g = f ∙ g #-}
{-# DISPLAY Cut._∘_ _ f g = _∘_ f g #-}

Hom-cut : ∀ {u v} {Ob : Type u} (_~_ : Ob → Ob → Type v) → Typeω
Hom-cut {Ob} _~_ = {y z : Ob} → Cut (λ (x : Ob) → x ~ y) (λ _ → y ~ z) λ x _ → x ~ z

Hom-cut-alt : ∀ {u v} {Ob : Type u} (_~_ : Ob → Ob → Type v) → Typeω
Hom-cut-alt {Ob} _~_ = {y z : Ob} → Cut-alt (λ (x : Ob) → x ~ y) (λ _ → y ~ z) λ x _ → x ~ z

open Cut-alt ⦃ ... ⦄ public
{-# DISPLAY Cut-alt.seq _ = _⨾_ #-}

instance
  Cut-alt→Cut : ∀ {u v w z} {A : Type u} {B : A → Type v} {C : A → Type w} {D : ∀ x → B x → Type z}
              → ⦃ cut : Cut-alt B C D ⦄ → Cut B C D
  Cut-alt→Cut ⦃ cut = cut ⦄ .Cut.seq = Cut-alt.seq cut
  {-# INCOHERENT Cut-alt→Cut #-}

record dCut {u v w z v' w' z'}
  {A : Type u}
  (B : A → Type v)
  (C : A → Type w)
  (D : ∀ x → B x → Type z)
  (B' : ∀ {x} → B x → B x → Type v')
  (C' : ∀ {x} → C x → C x → Type w')
  (D' : ∀ {x} {b b' : B x} → D x b → D x b' → Type z')
  : Typeω
  where
  constructor #dcut
  field
    ⦃ dCut-cut ⦄ : Cut B C D
    hconcat : ∀ {x} {b b' : B x} {c c' : C x} → B' b b' → C' c c' → D' (b ∙ c) (b' ∙ c')

  infixr 40 hconcat
  {-# INLINE hconcat #-}
{-# INLINE #dcut #-}

open dCut ⦃ ... ⦄ hiding (hconcat) public

_●_ : ∀ {u v w z v' w' z'} {A : Type u} {B : A → Type v} {C : A → Type w} {D : ∀ x → B x → Type z}
    → {B' : ∀ {x} → B x → B x → Type v'} {C' : ∀ {x} → C x → C x → Type w'}
    → {D' : ∀ {x} {b b' : B x} → D x b → D x b' → Type z'}
    → ⦃ dcut : dCut B C D B' C' D' ⦄
    → ∀ {x} {b b' : B x} {c c' : C x} → B' b b' → C' c c' → D' (b ∙ c) (b' ∙ c')
_●_ ⦃ dcut ⦄ = dCut.hconcat dcut
{-# DISPLAY dCut.hconcat _ = _●_ #-}

dHom-cut : ∀ {u v v₂} {Ob : Type u}
         → (Hom : Ob → Ob → Type v)
         → (Hom₂ : ∀ {x y} → Hom x y → Hom x y → Type v₂)
         → Typeω
dHom-cut {Ob} Hom Hom₂ =
  ∀ {y z : Ob} → dCut
    (λ x → Hom x y)
    (λ _ → Hom y z)
    (λ x _ → Hom x z)
    Hom₂
    Hom₂
    Hom₂

record Bicut {u v w z v' w' z'}
  {A : Type u}
  (B : A → Type v)
  (C : A → Type w)
  (D : ∀ x → B x → Type z)
  (B' : ∀ {x} → B x → B x → Type v')
  (C' : ∀ {x} → C x → C x → Type w')
  (D' : ∀ {x} {b b' : B x} → D x b → D x b' → Type z')
  : Typeω
  where
  constructor #hcut
  --infixr 40 hseq
  field
    ⦃ Bicut-dcut ⦄ : dCut B C D B' C' D'
    ⦃ Bicut-vcut ⦄ : ∀ {x} {b' b'' : B x} → Cut-alt (B' b') (λ b → B' b b'') (λ _ _ → B' b' b'')

Bihom-cut : ∀ {u v v₂} {Ob : Type u}
         → (Hom : Ob → Ob → Type v)
         → (Hom₂ : ∀ {x y} → Hom x y → Hom x y → Type v₂)
         → Typeω
Bihom-cut {Ob} Hom Hom₂ =
  ∀ {y z : Ob} → Bicut
    (λ x → Hom x y)
    (λ _ → Hom y z)
    (λ x _ → Hom x z)
    Hom₂
    Hom₂
    Hom₂


record Reasoning {u v} {A : Type u} (B : A → A → Type v) : Typeω where
  field
    ⦃ cut ⦄ : Hom-cut B
    fin : ∀ x → B x x

open Reasoning ⦃ ... ⦄ using () renaming (fin to infixl 50 _■) public
