I wanted to see what I could derive about the identity type with a very minimal
set of assumptions, implementing Sterling's reflexive graphs paper

```
{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Core.Identity where

open import Lib.Core.Prim

record Ids : Typeω where
  infix 2 _＝_
  field
    _＝_ : ∀ {u} {A : Type u} → A → A → Type u
    refl : ∀ {u} {A : Type u} {x : A} → x ＝ x
    𝓙 : ∀ {u v} {A : Type u} (C : (x y : A) → x ＝ y → Type v)
      → ((x : A) → C x x refl)
      → ∀ {x y} (w : x ＝ y) → C x y w
    Disp : ∀ {u v} {A : Type u} {B : A → Type v}
         → ∀ {x y} → x ＝ y → B x → B y → Type u -- note, we don't select a canonical reflexivity here

    -- a virtual definitional equality
    𝓙-refl : ∀ {u v} {A : Type u} (C : (x y : A) → x ＝ y → Type v)
           → (c : (a : A) → C a a refl)
           → (x : A) → (𝓙 C c refl) c x

  erefl : ∀ {u} {A : Type u} (x : A) → x ＝ x
  erefl x = refl {x = x}

  ap : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → ∀ {x y} → x ＝ y → f x ＝ f y
  ap f = 𝓙 (λ x y q → f x ＝ f y) (λ x → erefl (f x))

--   ap-refl : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) (x : A) → ap f (erefl x) ≡ erefl (f x)
--   ap-refl f = 𝓙-refl (λ x y q → f x ＝ f y) (λ x → erefl (f x))

--   sym : ∀ {u} {A : Type u} {x y : A} → x ＝ y → y ＝ x
--   sym = 𝓙 (λ x y p → y ＝ x) erefl

--   sym-refl : ∀ {u} {A : Type u} (x : A)
--            → sym refl ≡ (erefl x)
--   sym-refl = 𝓙-refl (λ x y p → y ＝ x) erefl

--   midpoint : ∀ {u} {A : Type u} {x y : A} → x ＝ y → A
--   midpoint {A = A} = 𝓙 (λ _ _ _ → A) id

--   midpoint-refl : ∀ {u} {A : Type u} (u : A) → midpoint (erefl u) ≡ u
--   midpoint-refl {A = A} = 𝓙-refl (λ _ _ _ → A) id

--   𝓙-idf : ∀ {u v} {A : Type u} (B : (x y : A) → x ＝ y → Type v)
--         → (let C = λ (x y : A) (p : x ＝ y) → B x y p → B x y p)
--         → (u : A) → 𝓙 C (λ x → idf (B x x refl)) refl ≡ idf (B u u refl)
--   𝓙-idf B = 𝓙-refl (λ x y p → B x y p → B x y p) (λ x → idf (B x x refl))

--   𝓙-id-refl : ∀ {u v} {A : Type u} (B : (x y : A) → x ＝ y → Type v)
--             → (let
--                 C = λ x y p → B x y p → B x y p
--                 φ = λ x → idf (B x x refl)
--                 D = λ x y p → (𝓙 C φ refl) ≡ id)
--             → (x : A) → 𝓙 D (𝓙-refl C φ) refl ≡ 𝓙-refl C φ x
--   𝓙-id-refl {A = A} B =
--     𝓙-refl (λ x y p → 𝓙 C (λ _ → id) refl ≡ idf (B x x refl)) (𝓙-refl C (λ _ → id)) where
--       C = λ (x y : A) (p : x ＝ y) → B x y p → B x y p

--   𝓙-2refl : ∀ {u v} {A : Type u} (B : (x y : A) → x ＝ y → Type v)
--           → (c : ∀ a → B a a refl) (a : A)
--           → 𝓙 (λ x _ _ → 𝓙 B c (erefl x) ≡ c x) (𝓙-refl B c) refl ≡ 𝓙-refl B c a
--   𝓙-2refl B c = 𝓙-refl (λ x y p → 𝓙 B c (erefl x) ≡ c x) (𝓙-refl B c)
--   -- one can actually keep going to 3, 4...

-- module _ {ids : Ids} where
--   open Ids ids
--   -- Principle 1: Identification induction
--   ind₌ : ∀ {u v} {A : Type u} (C : ∀ x y → x ＝ y → Type v)
--        → {x y : A} (p : x ＝ y) (c : (x : A) → C x x refl) → C x y p
--   ind₌ C p c = 𝓙 C c p

--   ind-refl : ∀ {u v} {A : Type u} (C : ∀ x y → x ＝ y → Type v)
--            → (c : (x : A) → C x x refl) {x : A}
--            → ind₌ C refl c ≡ c x
--   ind-refl C c {x} = 𝓙-refl C c x

--   -- Corollary 1: Transport
--   tr : ∀ {u v} {A : Type u} (B : A → Type v) {x y : A} → x ＝ y → B x → B y
--   tr {u} {v} {A} B {x = x} {y} p = ind₌ (λ x y _ → B x → B y) p (λ x → idf (B x))

--   idtofun : ∀ {u} {A B : Type u} → A ＝ B → A → B
--   idtofun = tr id

--   happly : ∀ {u v} {A : Type u} {B : A → Type v}
--          → {f g : ∀ a → B a} → f ＝ g → (x : A) → f x ＝ g x
--   happly {v = v} {A = A} {B} {f} {g} p x = ind₌ C p (λ f → erefl (f x)) where
--     C : (h k : ∀ a → B a) → h ＝ k → Type v
--     C h k _ = h x ＝ k x

--   happly-refl : ∀ {u v} {A : Type u} {B : A → Type v} (f : ∀ a → B a) {x : A}
--               → happly (erefl f) x ≡ erefl (f x)
--   happly-refl {v} {B} f {x} = ind-refl (λ h k _ → h x ＝ k x) (λ f → erefl (f x))

--   -- We can prove that transport on refl has equivalent action to id
--   -- directly from the id induction comp rule
--   tr-htpy : ∀ {u v} {A : Type u} (B : A → Type v) (x : A) → tr B (erefl x) ≡ id
--   tr-htpy B _ = ind-refl (λ x y _ → B x → B y) (λ _ b → b)

--   -- This is harder to do (without additional assumptions about the metatheory's equality)
--   tr-refl : ∀ {u v} {A : Type u} (B : A → Type v)
--           → {x : A} (b : B x) → tr B refl b ≡ b
--   tr-refl B {x} b = {!!} where
--     -- motive is `tr B refl b ≡ b`, we need to get this in a form like:
--     -- `𝓙 C (erefl x) c ≡ c x` where `∀ x → c x ≡ b` for some c, C.
--     -- Note: this means that `c` is weakly constant
--     --
--     -- But we could have it easily if we have the below assumptions re: our metatheory
--     --  1. transport in its Id
--     --  2. at least one self-homotopy over function application on f
--     module _
--       (t : {f g : B x → B x} → f ≡ g → ((h : B x → B x) → h b ≡ h b) → f b ≡ g b)
--       (d : (f : B x → B x) → f b ≡ f b)
--       where
--       meta-happly : {f g : B x → B x} → f ≡ g → f b ≡ g b
--       meta-happly q = t q d

--       goal : tr B refl b ≡ b
--       goal = meta-happly (tr-htpy B x)

--   -- Definition 2: Singleton type
--   ⟨_⟩₁ : ∀ {u} {A : Type u} (x : A) → Type u
--   ⟨_⟩₁ {A = A} x = Σ λ (y : A) → x ＝ y

--   -- Corollary 3: Contractibility of Singletons
--   singl-contr : ∀ {u} {A : Type u} {a : A} → ((x , q) : ⟨ a ⟩₁) → a , refl ＝ x , q
--   singl-contr {u} {A} (x , q) =
--     let
--       B : (x y : A) → x ＝ y → Type u
--       B = λ x y p → (x , refl {x = x}) ＝ (y , p)
--     in ind₌ B q (λ a → erefl (a , refl))

--   -- Based path induction. We'll follow Hofmann's proof cited by Sterling
--   -- (1lab uses this as well IIRC, but with subst2 instead)
--   J : ∀ {u v} {A : Type u} {x : A} (B : ∀ y → x ＝ y → Type v)
--     → B x refl → ∀ {y} (p : x ＝ y) → B y p
--   J {v} {x} B c {y} p = tr B♯ (singl-contr (y , p)) c where
--     B♯ : ⟨ x ⟩₁ → Type v
--     B♯ (y , p) = B y p
