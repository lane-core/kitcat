Applicative instance for List.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.List.Impl.Applicative where

open import Core.Type
open import Core.Base using (_≡_; refl; ap; sym; funext)
open import Core.Kan using (_∙_)
open import Core.Data.List.Type
open import Core.Data.List.Base
open import Core.Data.List.Properties
open import Core.Data.List.Impl.Map
open import Core.Trait.Effect
open import Core.Trait.Applicative using (Applicative)

private variable
  u v w : Level
  A B C : Type u

```

Private helpers for the applicative laws.

```agda

private
  _$_ : (A → B) → A → B
  f $ x = f x

  compose : (B → C) → (A → B) → A → C
  compose g f x = g (f x)

  ap-list : List (A → B) → List A → List B
  ap-list fs xs = concatMap (λ f → map f xs) fs

  pure-id-list : (v : List A) → ap-list ((λ x → x) ∷ []) v ≡ v
  pure-id-list v =
    cat.unitr (map (λ x → x) v)
    ∙ ap (λ h → h v) (funext map.id)

  interchange-proof
    : (u' : List (A → B)) (y : A)
    → ap-list u' (y ∷ []) ≡ ap-list ((_$ y) ∷ []) u'
  interchange-proof [] y = refl
  interchange-proof (f ∷ fs) y =
    ap ((f y ∷ []) ++_) (interchange-proof fs y)
    ∙ cat.assoc (f y ∷ []) (map (_$ y) fs) []

```

Instance declaration.

```agda

instance
  Applicative-List : Applicative (impl List)
  Applicative-List .Applicative.Map-Applicative = Map-List
  Applicative-List .Applicative.pure x = x ∷ []
  Applicative-List .Applicative._<*>_ = ap-list
  Applicative-List .Applicative.pure-id {v = v} =
    pure-id-list v
  Applicative-List .Applicative.pure-∘
    {u = gs} {v = fs} {w = xs} =
    pure-∘-proof gs fs xs
    where
    @0 ap-dist
      : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
      → (hs ks : List (X → Y)) (xs : List X)
      → ap-list (hs ++ ks) xs
        ≡ ap-list hs xs ++ ap-list ks xs
    ap-dist [] ks xs = refl
    ap-dist (h ∷ hs) ks xs =
      ap (map h xs ++_) (ap-dist hs ks xs)
      ∙ sym (cat.assoc (map h xs)
              (ap-list hs xs) (ap-list ks xs))

    @0 single-g
      : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
          {C : Type ℓ''}
      → (g : B → C) (fs : List (A → B)) (xs : List A)
      → ap-list (map (g ∘_) fs) xs
        ≡ map g (ap-list fs xs)
    single-g g [] xs = refl
    single-g g (f ∷ fs) xs =
      ap (map (g ∘ f) xs ++_) (single-g g fs xs)
      ∙ ap (_++ map g (ap-list fs xs))
          (map.comp g f xs)
      ∙ sym (map.cat g (map f xs)
              (ap-list fs xs))

    @0 pure-∘-proof
      : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
          {C : Type ℓ''}
      → (gs : List (B → C)) (fs : List (A → B))
        (xs : List A)
      → ap-list
          (ap-list (ap-list (compose ∷ []) gs) fs) xs
        ≡ ap-list gs (ap-list fs xs)
    pure-∘-proof [] fs xs = refl
    pure-∘-proof {A = A} {B = B} {C = C}
      (g ∷ gs) fs xs =
      let
        level1
          : ap-list
              (ap-list (compose ∷ []) (g ∷ gs)) fs
            ≡ ap-list
              ((g ∘_) ∷ map compose gs) fs
        level1 = ap (λ h → ap-list h fs)
          (cat.unitr ((g ∘_) ∷ map compose gs))

        level2
          : ap-list
              ((g ∘_) ∷ map compose gs) fs
            ≡ map (g ∘_) fs
              ++ ap-list (map compose gs) fs
        level2 =
          ap-dist {X = A → B} {Y = A → C}
            ((g ∘_) ∷ []) (map compose gs) fs
          ∙ ap (_++ ap-list (map compose gs) fs)
              (cat.unitr (map (g ∘_) fs))

        level3
          : ap-list (map (g ∘_) fs
              ++ ap-list (map compose gs) fs) xs
            ≡ ap-list (map (g ∘_) fs) xs
              ++ ap-list
                  (ap-list (map compose gs) fs) xs
        level3 =
          ap-dist {X = A} {Y = C}
            (map (g ∘_) fs)
            (ap-list (map compose gs) fs) xs

        first-part
          : ap-list (map (g ∘_) fs) xs
            ≡ map g (ap-list fs xs)
        first-part = single-g g fs xs

        second-part-eq
          : ap-list
              (ap-list (map compose gs) fs) xs
            ≡ ap-list
              (ap-list (map compose gs ++ []) fs) xs
        second-part-eq =
          ap (λ h → ap-list (ap-list h fs) xs)
            (sym (cat.unitr (map compose gs)))

        second-part
          : ap-list
              (ap-list (map compose gs ++ []) fs) xs
            ≡ ap-list gs (ap-list fs xs)
        second-part = pure-∘-proof gs fs xs
      in
        ap (λ h → ap-list h xs) (level1 ∙ level2)
      ∙ level3
      ∙ ap (_++ ap-list
              (ap-list (map compose gs) fs) xs)
          first-part
      ∙ ap (map g (ap-list fs xs) ++_)
          (second-part-eq ∙ second-part)
  Applicative-List .Applicative.pure-hom = refl
  Applicative-List .Applicative.pure-interchange
    {u = u'} {y} =
    interchange-proof u' y

```
